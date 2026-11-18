module

public import Papers.GraphicalZonotopes.DiamondBookGraph
public import Papers.GraphicalZonotopes.ThreeTreeConstruction

@[expose] public section
noncomputable section
namespace GraphicalZonotopes.DiamondBook
open Finset
open scoped BigOperators Pointwise
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 8192

instance decidableCliqueGraph {V : Type*} [DecidableEq V] (C : Finset V) :
    DecidableRel (cliqueGraph C).Adj :=
  fun x y => inferInstanceAs (Decidable (x≠y ∧ x∈C ∧ y∈C))
instance decidableAttachmentStar {V : Type*} [DecidableEq V] (x : V) (T : Finset V) :
    DecidableRel (attachmentStar x T).Adj :=
  fun y z => inferInstanceAs (Decidable (y≠z ∧ ((y=x ∧ z∈T) ∨ (z=x ∧ y∈T))))

theorem admissible_of_tetrahedron_list {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (F : Finset (Finset V)) (hF : tetrahedra G=F)
    (hcap : ∀ T∈F.biUnion (fun C => C.powerset.filter (fun T => T.card=3)),
      (F.filter (fun C => T⊆C)).card≤3) : Admissible G := by
  classical
  intro T hT hc
  rw [triangleMultiplicity,hF]
  by_cases he : (F.filter (fun C => T⊆C)).Nonempty
  · obtain ⟨C,hC⟩:=he
    obtain ⟨hCF,hTC⟩:=mem_filter.mp hC
    exact hcap T (mem_biUnion.mpr ⟨C,hCF,mem_filter.mpr ⟨mem_powerset.mpr hTC,hT⟩⟩)
  · rw [not_nonempty_iff_eq_empty.mp he,card_empty]
    norm_num

def small1G0 : SimpleGraph (Fin 5) := cliqueGraph {0,1,2,4}
instance small1dec0 : DecidableRel small1G0.Adj := by unfold small1G0; infer_instance
theorem small1tree0 : ThreeTreeOn ({0,1,2,4} : Finset (Fin 5)) small1G0 :=
  ThreeTreeOn.tetrahedron _ (by decide +kernel)
def small1F0 : Finset (Finset (Fin 5)) := {{0,1,2,4}}
theorem small1tetra0 : tetrahedra small1G0=small1F0 :=
  tetrahedra_cliqueGraph (by decide +kernel)

def small1G1 : SimpleGraph (Fin 5) := small1G0 ⊔ attachmentStar 3 {0,1,4}
instance small1dec1 : DecidableRel small1G1.Adj := by unfold small1G1; infer_instance
theorem small1clique1 : small1G0.IsClique ({0,1,4} : Finset (Fin 5)) := by
  unfold small1G0
  decide +kernel
theorem small1tree1 : ThreeTreeOn ({0,1,2,4,3} : Finset (Fin 5)) small1G1 := by
  have h:=ThreeTreeOn.attach small1tree0 (3 : Fin 5) (by decide +kernel)
    ({0,1,4} : Finset (Fin 5)) (by decide +kernel) (by decide +kernel) small1clique1
  simpa only [small1G1,show insert (3 : Fin 5) ({0,1,2,4} : Finset (Fin 5))={0,1,2,4,3} from by decide +kernel] using h
def small1F1 : Finset (Finset (Fin 5)) := insert (insert 3 {0,1,4}) small1F0
theorem small1tetra1 : tetrahedra small1G1=small1F1 := by
  rw [small1G1,tetrahedra_after_attachment small1tree0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small1clique1,small1tetra0]
  rfl

theorem small1spanning : IsThreeTree small1G1 := by
  change ThreeTreeOn univ small1G1
  have he : ({0,1,2,4,3} : Finset (Fin 5))=univ := by decide +kernel
  simpa only [he] using small1tree1

theorem small1admissible : Admissible small1G1 := by
  apply admissible_of_tetrahedron_list small1G1 small1F1 small1tetra1
  intro T hT
  unfold small1F1 small1F0 at hT ⊢
  fin_cases hT <;> decide +kernel

theorem small1subgraph : small1G1≤graph 1 := by
  change ∀ x y,small1G1.Adj x y → (graph 1).Adj x y
  unfold small1G1 small1G0
  decide +kernel

def small2G0 : SimpleGraph (Fin 6) := cliqueGraph {0,1,2,4}
instance small2dec0 : DecidableRel small2G0.Adj := by unfold small2G0; infer_instance
theorem small2tree0 : ThreeTreeOn ({0,1,2,4} : Finset (Fin 6)) small2G0 :=
  ThreeTreeOn.tetrahedron _ (by decide +kernel)
def small2F0 : Finset (Finset (Fin 6)) := {{0,1,2,4}}
theorem small2tetra0 : tetrahedra small2G0=small2F0 :=
  tetrahedra_cliqueGraph (by decide +kernel)

def small2G1 : SimpleGraph (Fin 6) := small2G0 ⊔ attachmentStar 3 {0,1,4}
instance small2dec1 : DecidableRel small2G1.Adj := by unfold small2G1; infer_instance
theorem small2clique1 : small2G0.IsClique ({0,1,4} : Finset (Fin 6)) := by
  unfold small2G0
  decide +kernel
theorem small2tree1 : ThreeTreeOn ({0,1,2,4,3} : Finset (Fin 6)) small2G1 := by
  have h:=ThreeTreeOn.attach small2tree0 (3 : Fin 6) (by decide +kernel)
    ({0,1,4} : Finset (Fin 6)) (by decide +kernel) (by decide +kernel) small2clique1
  simpa only [small2G1,show insert (3 : Fin 6) ({0,1,2,4} : Finset (Fin 6))={0,1,2,4,3} from by decide +kernel] using h
def small2F1 : Finset (Finset (Fin 6)) := insert (insert 3 {0,1,4}) small2F0
theorem small2tetra1 : tetrahedra small2G1=small2F1 := by
  rw [small2G1,tetrahedra_after_attachment small2tree0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small2clique1,small2tetra0]
  rfl

def small2G2 : SimpleGraph (Fin 6) := small2G1 ⊔ attachmentStar 5 {0,1,2}
instance small2dec2 : DecidableRel small2G2.Adj := by unfold small2G2; infer_instance
theorem small2clique2 : small2G1.IsClique ({0,1,2} : Finset (Fin 6)) := by
  unfold small2G1 small2G0
  decide +kernel
theorem small2tree2 : ThreeTreeOn ({0,1,2,4,3,5} : Finset (Fin 6)) small2G2 := by
  have h:=ThreeTreeOn.attach small2tree1 (5 : Fin 6) (by decide +kernel)
    ({0,1,2} : Finset (Fin 6)) (by decide +kernel) (by decide +kernel) small2clique2
  simpa only [small2G2,show insert (5 : Fin 6) ({0,1,2,4,3} : Finset (Fin 6))={0,1,2,4,3,5} from by decide +kernel] using h
def small2F2 : Finset (Finset (Fin 6)) := insert (insert 5 {0,1,2}) small2F1
theorem small2tetra2 : tetrahedra small2G2=small2F2 := by
  rw [small2G2,tetrahedra_after_attachment small2tree1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small2clique2,small2tetra1]
  rfl

theorem small2spanning : IsThreeTree small2G2 := by
  change ThreeTreeOn univ small2G2
  have he : ({0,1,2,4,3,5} : Finset (Fin 6))=univ := by decide +kernel
  simpa only [he] using small2tree2

theorem small2admissible : Admissible small2G2 := by
  apply admissible_of_tetrahedron_list small2G2 small2F2 small2tetra2
  intro T hT
  unfold small2F2 small2F1 small2F0 at hT ⊢
  fin_cases hT <;> decide +kernel

theorem small2subgraph : small2G2≤graph 2 := by
  change ∀ x y,small2G2.Adj x y → (graph 2).Adj x y
  unfold small2G2 small2G1 small2G0
  decide +kernel

def small3G0 : SimpleGraph (Fin 7) := cliqueGraph {0,1,2,4}
instance small3dec0 : DecidableRel small3G0.Adj := by unfold small3G0; infer_instance
theorem small3tree0 : ThreeTreeOn ({0,1,2,4} : Finset (Fin 7)) small3G0 :=
  ThreeTreeOn.tetrahedron _ (by decide +kernel)
def small3F0 : Finset (Finset (Fin 7)) := {{0,1,2,4}}
theorem small3tetra0 : tetrahedra small3G0=small3F0 :=
  tetrahedra_cliqueGraph (by decide +kernel)

def small3G1 : SimpleGraph (Fin 7) := small3G0 ⊔ attachmentStar 3 {0,1,4}
instance small3dec1 : DecidableRel small3G1.Adj := by unfold small3G1; infer_instance
theorem small3clique1 : small3G0.IsClique ({0,1,4} : Finset (Fin 7)) := by
  unfold small3G0
  decide +kernel
theorem small3tree1 : ThreeTreeOn ({0,1,2,4,3} : Finset (Fin 7)) small3G1 := by
  have h:=ThreeTreeOn.attach small3tree0 (3 : Fin 7) (by decide +kernel)
    ({0,1,4} : Finset (Fin 7)) (by decide +kernel) (by decide +kernel) small3clique1
  simpa only [small3G1,show insert (3 : Fin 7) ({0,1,2,4} : Finset (Fin 7))={0,1,2,4,3} from by decide +kernel] using h
def small3F1 : Finset (Finset (Fin 7)) := insert (insert 3 {0,1,4}) small3F0
theorem small3tetra1 : tetrahedra small3G1=small3F1 := by
  rw [small3G1,tetrahedra_after_attachment small3tree0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small3clique1,small3tetra0]
  rfl

def small3G2 : SimpleGraph (Fin 7) := small3G1 ⊔ attachmentStar 5 {0,1,2}
instance small3dec2 : DecidableRel small3G2.Adj := by unfold small3G2; infer_instance
theorem small3clique2 : small3G1.IsClique ({0,1,2} : Finset (Fin 7)) := by
  unfold small3G1 small3G0
  decide +kernel
theorem small3tree2 : ThreeTreeOn ({0,1,2,4,3,5} : Finset (Fin 7)) small3G2 := by
  have h:=ThreeTreeOn.attach small3tree1 (5 : Fin 7) (by decide +kernel)
    ({0,1,2} : Finset (Fin 7)) (by decide +kernel) (by decide +kernel) small3clique2
  simpa only [small3G2,show insert (5 : Fin 7) ({0,1,2,4,3} : Finset (Fin 7))={0,1,2,4,3,5} from by decide +kernel] using h
def small3F2 : Finset (Finset (Fin 7)) := insert (insert 5 {0,1,2}) small3F1
theorem small3tetra2 : tetrahedra small3G2=small3F2 := by
  rw [small3G2,tetrahedra_after_attachment small3tree1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small3clique2,small3tetra1]
  rfl

def small3G3 : SimpleGraph (Fin 7) := small3G2 ⊔ attachmentStar 6 {0,1,2}
instance small3dec3 : DecidableRel small3G3.Adj := by unfold small3G3; infer_instance
theorem small3clique3 : small3G2.IsClique ({0,1,2} : Finset (Fin 7)) := by
  unfold small3G2 small3G1 small3G0
  decide +kernel
theorem small3tree3 : ThreeTreeOn ({0,1,2,4,3,5,6} : Finset (Fin 7)) small3G3 := by
  have h:=ThreeTreeOn.attach small3tree2 (6 : Fin 7) (by decide +kernel)
    ({0,1,2} : Finset (Fin 7)) (by decide +kernel) (by decide +kernel) small3clique3
  simpa only [small3G3,show insert (6 : Fin 7) ({0,1,2,4,3,5} : Finset (Fin 7))={0,1,2,4,3,5,6} from by decide +kernel] using h
def small3F3 : Finset (Finset (Fin 7)) := insert (insert 6 {0,1,2}) small3F2
theorem small3tetra3 : tetrahedra small3G3=small3F3 := by
  rw [small3G3,tetrahedra_after_attachment small3tree2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small3clique3,small3tetra2]
  rfl

theorem small3spanning : IsThreeTree small3G3 := by
  change ThreeTreeOn univ small3G3
  have he : ({0,1,2,4,3,5,6} : Finset (Fin 7))=univ := by decide +kernel
  simpa only [he] using small3tree3

theorem small3admissible : Admissible small3G3 := by
  apply admissible_of_tetrahedron_list small3G3 small3F3 small3tetra3
  intro T hT
  unfold small3F3 small3F2 small3F1 small3F0 at hT ⊢
  fin_cases hT <;> decide +kernel

theorem small3subgraph : small3G3≤graph 3 := by
  change ∀ x y,small3G3.Adj x y → (graph 3).Adj x y
  unfold small3G3 small3G2 small3G1 small3G0
  decide +kernel

def small4G0 : SimpleGraph (Fin 8) := cliqueGraph {0,1,2,4}
instance small4dec0 : DecidableRel small4G0.Adj := by unfold small4G0; infer_instance
theorem small4tree0 : ThreeTreeOn ({0,1,2,4} : Finset (Fin 8)) small4G0 :=
  ThreeTreeOn.tetrahedron _ (by decide +kernel)
def small4F0 : Finset (Finset (Fin 8)) := {{0,1,2,4}}
theorem small4tetra0 : tetrahedra small4G0=small4F0 :=
  tetrahedra_cliqueGraph (by decide +kernel)

def small4G1 : SimpleGraph (Fin 8) := small4G0 ⊔ attachmentStar 3 {0,1,4}
instance small4dec1 : DecidableRel small4G1.Adj := by unfold small4G1; infer_instance
theorem small4clique1 : small4G0.IsClique ({0,1,4} : Finset (Fin 8)) := by
  unfold small4G0
  decide +kernel
theorem small4tree1 : ThreeTreeOn ({0,1,2,4,3} : Finset (Fin 8)) small4G1 := by
  have h:=ThreeTreeOn.attach small4tree0 (3 : Fin 8) (by decide +kernel)
    ({0,1,4} : Finset (Fin 8)) (by decide +kernel) (by decide +kernel) small4clique1
  simpa only [small4G1,show insert (3 : Fin 8) ({0,1,2,4} : Finset (Fin 8))={0,1,2,4,3} from by decide +kernel] using h
def small4F1 : Finset (Finset (Fin 8)) := insert (insert 3 {0,1,4}) small4F0
theorem small4tetra1 : tetrahedra small4G1=small4F1 := by
  rw [small4G1,tetrahedra_after_attachment small4tree0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small4clique1,small4tetra0]
  rfl

def small4G2 : SimpleGraph (Fin 8) := small4G1 ⊔ attachmentStar 5 {0,1,2}
instance small4dec2 : DecidableRel small4G2.Adj := by unfold small4G2; infer_instance
theorem small4clique2 : small4G1.IsClique ({0,1,2} : Finset (Fin 8)) := by
  unfold small4G1 small4G0
  decide +kernel
theorem small4tree2 : ThreeTreeOn ({0,1,2,4,3,5} : Finset (Fin 8)) small4G2 := by
  have h:=ThreeTreeOn.attach small4tree1 (5 : Fin 8) (by decide +kernel)
    ({0,1,2} : Finset (Fin 8)) (by decide +kernel) (by decide +kernel) small4clique2
  simpa only [small4G2,show insert (5 : Fin 8) ({0,1,2,4,3} : Finset (Fin 8))={0,1,2,4,3,5} from by decide +kernel] using h
def small4F2 : Finset (Finset (Fin 8)) := insert (insert 5 {0,1,2}) small4F1
theorem small4tetra2 : tetrahedra small4G2=small4F2 := by
  rw [small4G2,tetrahedra_after_attachment small4tree1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small4clique2,small4tetra1]
  rfl

def small4G3 : SimpleGraph (Fin 8) := small4G2 ⊔ attachmentStar 6 {0,1,2}
instance small4dec3 : DecidableRel small4G3.Adj := by unfold small4G3; infer_instance
theorem small4clique3 : small4G2.IsClique ({0,1,2} : Finset (Fin 8)) := by
  unfold small4G2 small4G1 small4G0
  decide +kernel
theorem small4tree3 : ThreeTreeOn ({0,1,2,4,3,5,6} : Finset (Fin 8)) small4G3 := by
  have h:=ThreeTreeOn.attach small4tree2 (6 : Fin 8) (by decide +kernel)
    ({0,1,2} : Finset (Fin 8)) (by decide +kernel) (by decide +kernel) small4clique3
  simpa only [small4G3,show insert (6 : Fin 8) ({0,1,2,4,3,5} : Finset (Fin 8))={0,1,2,4,3,5,6} from by decide +kernel] using h
def small4F3 : Finset (Finset (Fin 8)) := insert (insert 6 {0,1,2}) small4F2
theorem small4tetra3 : tetrahedra small4G3=small4F3 := by
  rw [small4G3,tetrahedra_after_attachment small4tree2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small4clique3,small4tetra2]
  rfl

def small4G4 : SimpleGraph (Fin 8) := small4G3 ⊔ attachmentStar 7 {0,1,3}
instance small4dec4 : DecidableRel small4G4.Adj := by unfold small4G4; infer_instance
theorem small4clique4 : small4G3.IsClique ({0,1,3} : Finset (Fin 8)) := by
  unfold small4G3 small4G2 small4G1 small4G0
  decide +kernel
theorem small4tree4 : ThreeTreeOn ({0,1,2,4,3,5,6,7} : Finset (Fin 8)) small4G4 := by
  have h:=ThreeTreeOn.attach small4tree3 (7 : Fin 8) (by decide +kernel)
    ({0,1,3} : Finset (Fin 8)) (by decide +kernel) (by decide +kernel) small4clique4
  simpa only [small4G4,show insert (7 : Fin 8) ({0,1,2,4,3,5,6} : Finset (Fin 8))={0,1,2,4,3,5,6,7} from by decide +kernel] using h
def small4F4 : Finset (Finset (Fin 8)) := insert (insert 7 {0,1,3}) small4F3
theorem small4tetra4 : tetrahedra small4G4=small4F4 := by
  rw [small4G4,tetrahedra_after_attachment small4tree3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small4clique4,small4tetra3]
  rfl

theorem small4spanning : IsThreeTree small4G4 := by
  change ThreeTreeOn univ small4G4
  have he : ({0,1,2,4,3,5,6,7} : Finset (Fin 8))=univ := by decide +kernel
  simpa only [he] using small4tree4

theorem small4admissible : Admissible small4G4 := by
  apply admissible_of_tetrahedron_list small4G4 small4F4 small4tetra4
  intro T hT
  unfold small4F4 small4F3 small4F2 small4F1 small4F0 at hT ⊢
  fin_cases hT <;> decide +kernel

theorem small4subgraph : small4G4≤graph 4 := by
  change ∀ x y,small4G4.Adj x y → (graph 4).Adj x y
  unfold small4G4 small4G3 small4G2 small4G1 small4G0
  decide +kernel

def small5G0 : SimpleGraph (Fin 9) := cliqueGraph {0,1,2,4}
instance small5dec0 : DecidableRel small5G0.Adj := by unfold small5G0; infer_instance
theorem small5tree0 : ThreeTreeOn ({0,1,2,4} : Finset (Fin 9)) small5G0 :=
  ThreeTreeOn.tetrahedron _ (by decide +kernel)
def small5F0 : Finset (Finset (Fin 9)) := {{0,1,2,4}}
theorem small5tetra0 : tetrahedra small5G0=small5F0 :=
  tetrahedra_cliqueGraph (by decide +kernel)

def small5G1 : SimpleGraph (Fin 9) := small5G0 ⊔ attachmentStar 3 {0,1,4}
instance small5dec1 : DecidableRel small5G1.Adj := by unfold small5G1; infer_instance
theorem small5clique1 : small5G0.IsClique ({0,1,4} : Finset (Fin 9)) := by
  unfold small5G0
  decide +kernel
theorem small5tree1 : ThreeTreeOn ({0,1,2,4,3} : Finset (Fin 9)) small5G1 := by
  have h:=ThreeTreeOn.attach small5tree0 (3 : Fin 9) (by decide +kernel)
    ({0,1,4} : Finset (Fin 9)) (by decide +kernel) (by decide +kernel) small5clique1
  simpa only [small5G1,show insert (3 : Fin 9) ({0,1,2,4} : Finset (Fin 9))={0,1,2,4,3} from by decide +kernel] using h
def small5F1 : Finset (Finset (Fin 9)) := insert (insert 3 {0,1,4}) small5F0
theorem small5tetra1 : tetrahedra small5G1=small5F1 := by
  rw [small5G1,tetrahedra_after_attachment small5tree0
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small5clique1,small5tetra0]
  rfl

def small5G2 : SimpleGraph (Fin 9) := small5G1 ⊔ attachmentStar 5 {0,1,2}
instance small5dec2 : DecidableRel small5G2.Adj := by unfold small5G2; infer_instance
theorem small5clique2 : small5G1.IsClique ({0,1,2} : Finset (Fin 9)) := by
  unfold small5G1 small5G0
  decide +kernel
theorem small5tree2 : ThreeTreeOn ({0,1,2,4,3,5} : Finset (Fin 9)) small5G2 := by
  have h:=ThreeTreeOn.attach small5tree1 (5 : Fin 9) (by decide +kernel)
    ({0,1,2} : Finset (Fin 9)) (by decide +kernel) (by decide +kernel) small5clique2
  simpa only [small5G2,show insert (5 : Fin 9) ({0,1,2,4,3} : Finset (Fin 9))={0,1,2,4,3,5} from by decide +kernel] using h
def small5F2 : Finset (Finset (Fin 9)) := insert (insert 5 {0,1,2}) small5F1
theorem small5tetra2 : tetrahedra small5G2=small5F2 := by
  rw [small5G2,tetrahedra_after_attachment small5tree1
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small5clique2,small5tetra1]
  rfl

def small5G3 : SimpleGraph (Fin 9) := small5G2 ⊔ attachmentStar 6 {0,1,2}
instance small5dec3 : DecidableRel small5G3.Adj := by unfold small5G3; infer_instance
theorem small5clique3 : small5G2.IsClique ({0,1,2} : Finset (Fin 9)) := by
  unfold small5G2 small5G1 small5G0
  decide +kernel
theorem small5tree3 : ThreeTreeOn ({0,1,2,4,3,5,6} : Finset (Fin 9)) small5G3 := by
  have h:=ThreeTreeOn.attach small5tree2 (6 : Fin 9) (by decide +kernel)
    ({0,1,2} : Finset (Fin 9)) (by decide +kernel) (by decide +kernel) small5clique3
  simpa only [small5G3,show insert (6 : Fin 9) ({0,1,2,4,3,5} : Finset (Fin 9))={0,1,2,4,3,5,6} from by decide +kernel] using h
def small5F3 : Finset (Finset (Fin 9)) := insert (insert 6 {0,1,2}) small5F2
theorem small5tetra3 : tetrahedra small5G3=small5F3 := by
  rw [small5G3,tetrahedra_after_attachment small5tree2
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small5clique3,small5tetra2]
  rfl

def small5G4 : SimpleGraph (Fin 9) := small5G3 ⊔ attachmentStar 7 {0,1,3}
instance small5dec4 : DecidableRel small5G4.Adj := by unfold small5G4; infer_instance
theorem small5clique4 : small5G3.IsClique ({0,1,3} : Finset (Fin 9)) := by
  unfold small5G3 small5G2 small5G1 small5G0
  decide +kernel
theorem small5tree4 : ThreeTreeOn ({0,1,2,4,3,5,6,7} : Finset (Fin 9)) small5G4 := by
  have h:=ThreeTreeOn.attach small5tree3 (7 : Fin 9) (by decide +kernel)
    ({0,1,3} : Finset (Fin 9)) (by decide +kernel) (by decide +kernel) small5clique4
  simpa only [small5G4,show insert (7 : Fin 9) ({0,1,2,4,3,5,6} : Finset (Fin 9))={0,1,2,4,3,5,6,7} from by decide +kernel] using h
def small5F4 : Finset (Finset (Fin 9)) := insert (insert 7 {0,1,3}) small5F3
theorem small5tetra4 : tetrahedra small5G4=small5F4 := by
  rw [small5G4,tetrahedra_after_attachment small5tree3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small5clique4,small5tetra3]
  rfl

def small5G5 : SimpleGraph (Fin 9) := small5G4 ⊔ attachmentStar 8 {0,1,3}
instance small5dec5 : DecidableRel small5G5.Adj := by unfold small5G5; infer_instance
theorem small5clique5 : small5G4.IsClique ({0,1,3} : Finset (Fin 9)) := by
  unfold small5G4 small5G3 small5G2 small5G1 small5G0
  decide +kernel
theorem small5tree5 : ThreeTreeOn ({0,1,2,4,3,5,6,7,8} : Finset (Fin 9)) small5G5 := by
  have h:=ThreeTreeOn.attach small5tree4 (8 : Fin 9) (by decide +kernel)
    ({0,1,3} : Finset (Fin 9)) (by decide +kernel) (by decide +kernel) small5clique5
  simpa only [small5G5,show insert (8 : Fin 9) ({0,1,2,4,3,5,6,7} : Finset (Fin 9))={0,1,2,4,3,5,6,7,8} from by decide +kernel] using h
def small5F5 : Finset (Finset (Fin 9)) := insert (insert 8 {0,1,3}) small5F4
theorem small5tetra5 : tetrahedra small5G5=small5F5 := by
  rw [small5G5,tetrahedra_after_attachment small5tree4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) small5clique5,small5tetra4]
  rfl

theorem small5spanning : IsThreeTree small5G5 := by
  change ThreeTreeOn univ small5G5
  have he : ({0,1,2,4,3,5,6,7,8} : Finset (Fin 9))=univ := by decide +kernel
  simpa only [he] using small5tree5

theorem small5admissible : Admissible small5G5 := by
  apply admissible_of_tetrahedron_list small5G5 small5F5 small5tetra5
  intro T hT
  unfold small5F5 small5F4 small5F3 small5F2 small5F1 small5F0 at hT ⊢
  fin_cases hT <;> decide +kernel

theorem small5subgraph : small5G5≤graph 5 := by
  change ∀ x y,small5G5.Adj x y → (graph 5).Adj x y
  unfold small5G5 small5G4 small5G3 small5G2 small5G1 small5G0
  decide +kernel

/-- Every member below the diamond threshold has an admissible spanning
3-tree. The finite cases exhaust the exact parameter range1≤k≤5. -/
theorem admissible_spanning_small (k : ℕ) (hk : 1≤k) (hmax : k≤5) :
    HasAdmissibleSpanningThreeTree (graph k) := by
  interval_cases k
  · exact ⟨small1G1,small1subgraph,small1spanning,small1admissible⟩
  · exact ⟨small2G2,small2subgraph,small2spanning,small2admissible⟩
  · exact ⟨small3G3,small3subgraph,small3spanning,small3admissible⟩
  · exact ⟨small4G4,small4subgraph,small4spanning,small4admissible⟩
  · exact ⟨small5G5,small5subgraph,small5spanning,small5admissible⟩

end GraphicalZonotopes.DiamondBook
