module

public import Papers.GraphicalZonotopes.ThreeTreeStates

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev AllIncidentClique (G : SimpleGraph V) (T : ↥(triangles G)) :=
  {C : ↥(tetrahedra G) // T.1⊆C.1}

def faceMissing (G : SimpleGraph V) (C : ↥(tetrahedra G)) (T : ↥(triangles G))
    (hTC : T.1⊆C.1) : ↥C.1 :=
  Classical.choose (exists_opposite (mem_filter.mp C.2).2.1 (mem_triangles.mp T.2).1 hTC)

theorem faceMissing_spec (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(triangles G)) (hTC : T.1⊆C.1) :
    C.1.erase (faceMissing G C T hTC).1=T.1 :=
  Classical.choose_spec (exists_opposite (mem_filter.mp C.2).2.1
    (mem_triangles.mp T.2).1 hTC)

theorem faceMissing_notMem (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(triangles G)) (hTC : T.1⊆C.1) :
    (faceMissing G C T hTC).1∉T.1 := by
  rw [← faceMissing_spec G C T hTC]
  exact notMem_erase _ _

def faceRow (G : SimpleGraph V) (s : CompatibleRows G)
    (T : ↥(triangles G)) (C : AllIncidentClique G T) (j : ↥T.1) : Bool :=
  (s.clique C.1).row (faceMissing G C.1 T C.2) ⟨j.1,C.2 j.2⟩

def columnValue (G : SimpleGraph V) (s : CompatibleRows G)
    (T : ↥(triangles G)) (j : ↥T.1) : ℝ :=
  ∑ C : AllIncidentClique G T,realBit (faceRow G s T C j)

def allIncidentCliqueEquiv (G : SimpleGraph V) (T : ↥(triangles G)) :
    AllIncidentClique G T ≃ ↥((tetrahedra G).filter (fun C => T.1⊆C)) where
  toFun C := ⟨C.1.1,mem_filter.mpr ⟨C.1.2,C.2⟩⟩
  invFun C := ⟨⟨C.1,(mem_filter.mp C.2).1⟩,(mem_filter.mp C.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem allIncidentClique_card (G : SimpleGraph V) (T : ↥(triangles G)) :
    Fintype.card (AllIncidentClique G T)=triangleMultiplicity G T.1 := by
  classical
  rw [Fintype.card_congr (allIncidentCliqueEquiv G T),Fintype.card_coe]
  rfl

theorem internal_column (G : SimpleGraph V) (s : CompatibleRows G)
    (T : ↥(triangles G)) (hT : T.1∈internalTriangles G) (j : ↥T.1) :
    columnValue G s T j=((s.triangle ⟨T.1,hT⟩).degree : ℝ) := by
  let T' : ↥(internalTriangles G) := ⟨T.1,hT⟩
  have he : ∀ C : AllIncidentClique G T,
      faceRow G s T C j=(s.triangle T').row C j := by
    intro C
    exact congrArg (fun f : ↥T.1 → Bool => f j) (s.port_eq C.1 T' C.2)
  unfold columnValue
  simp_rw [he]
  exact (s.triangle T').sum_row j

/-- The column sums on every actual triangle, including the leaf
triangles, are constants in {0,1,2}. The leaf case is proved from its actual
single incident tetrahedron, rather than assigned an unproved response. -/
theorem column_constant {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    (s : CompatibleRows G) (T : ↥(triangles G)) :
    ∃ d : ℕ,(d=0 ∨ d=1 ∨ d=2) ∧ ∀ j : ↥T.1,columnValue G s T j=(d : ℝ) := by
  classical
  by_cases hT : T.1∈internalTriangles G
  · refine ⟨(s.triangle ⟨T.1,hT⟩).degree,?_,internal_column G s T hT⟩
    exact Or.inr (s.triangle ⟨T.1,hT⟩).degree_mem
  · have htri := mem_triangles.mp T.2
    obtain ⟨C,hC,hTC⟩ := h.triangle_extends htri.1 htri.2
    have hpos : 0<triangleMultiplicity G T.1 := by
      apply card_pos.mpr
      exact ⟨C,mem_filter.mpr ⟨hC,hTC⟩⟩
    have hsmall : ¬2≤triangleMultiplicity G T.1 := fun hcount =>
      hT (mem_internalTriangles.mpr ⟨T.2,hcount⟩)
    have hone : Fintype.card (AllIncidentClique G T)=1 := by
      rw [allIncidentClique_card]
      omega
    obtain ⟨C₀,hunique⟩ := Fintype.card_eq_one_iff.mp hone
    let p := faceMissing G C₀.1 T C₀.2
    have hleaf : C₀.1.1.erase p.1∉internalTriangles G := by
      rw [faceMissing_spec G C₀.1 T C₀.2]
      exact hT
    obtain ⟨b,hb⟩ := (s.clique C₀.1).constant p hleaf
    have hcol : ∀ j : ↥T.1,columnValue G s T j=realBit b := by
      intro j
      unfold columnValue
      rw [sum_eq_single C₀]
      · apply congrArg realBit
        apply hb
        intro he
        exact faceMissing_notMem G C₀.1 T C₀.2
          ((congrArg Subtype.val he) ▸ j.2)
      · intro D hD hne
        exact False.elim (hne (hunique D))
      · intro hn
        exact False.elim (hn (mem_univ C₀))
    cases hbval : b
    · exact ⟨0,Or.inl rfl,fun j => by simpa [hbval,realBit] using hcol j⟩
    · exact ⟨1,Or.inr (Or.inl rfl),fun j => by simpa [hbval,realBit] using hcol j⟩

def triangleWeight {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    (s : CompatibleRows G) (T : ↥(triangles G)) : ℕ :=
  Classical.choose (column_constant h s T)

theorem triangleWeight_mem {S : Finset V} {G : SimpleGraph V} (h : ThreeTreeOn S G)
    (s : CompatibleRows G) (T : ↥(triangles G)) :
    triangleWeight h s T=0 ∨ triangleWeight h s T=1 ∨ triangleWeight h s T=2 :=
  (Classical.choose_spec (column_constant h s T)).1

theorem column_eq_triangleWeight {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (s : CompatibleRows G) (T : ↥(triangles G)) (j : ↥T.1) :
    columnValue G s T j=(triangleWeight h s T : ℝ) :=
  (Classical.choose_spec (column_constant h s T)).2 j

end ThreeTreeStates
end GraphicalZonotopes
