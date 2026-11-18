module

public import Papers.GraphicalZonotopes.PrunedIncidence
public import Papers.GraphicalZonotopes.FourState
public import Papers.GraphicalZonotopes.TriangleState
public import Papers.GraphicalZonotopes.TreeCompatibility
public import Mathlib.Data.Sigma.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace ThreeTreeStates
open Finset
open RootedResponse
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_opposite {C T : Finset V} (hC : C.card=4) (hT : T.card=3)
    (hTC : T⊆C) : ∃ r : ↥C,C.erase r.1=T := by
  have hcard : (C\T).card=1 := by rw [card_sdiff_of_subset hTC,hC,hT]
  obtain ⟨r,hr⟩ := card_eq_one.mp hcard
  have hrmem : r∈C\T := by rw [hr]; simp
  obtain ⟨hrC,hrT⟩ := mem_sdiff.mp hrmem
  refine ⟨⟨r,hrC⟩,?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hxr,hxC⟩ := mem_erase.mp hx
    by_contra hxT
    have hxs : x∈C\T := mem_sdiff.mpr ⟨hxC,hxT⟩
    rw [hr,mem_singleton] at hxs
    exact hxr hxs
  · intro hxT
    exact mem_erase.mpr ⟨fun hxr => hrT (by simpa only [hxr] using hxT),hTC hxT⟩

def opposite (G : SimpleGraph V) (C : ↥(tetrahedra G)) (T : ↥(internalTriangles G))
    (hTC : T.1⊆C.1) : ↥C.1 :=
  Classical.choose (exists_opposite (mem_filter.mp C.2).2.1
    (mem_triangles.mp (mem_internalTriangles.mp T.2).1).1 hTC)

theorem opposite_spec (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(internalTriangles G)) (hTC : T.1⊆C.1) :
    C.1.erase (opposite G C T hTC).1=T.1 :=
  Classical.choose_spec (exists_opposite (mem_filter.mp C.2).2.1
    (mem_triangles.mp (mem_internalTriangles.mp T.2).1).1 hTC)

theorem opposite_notMem (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(internalTriangles G)) (hTC : T.1⊆C.1) :
    (opposite G C T hTC).1∉T.1 := by
  rw [← opposite_spec G C T hTC]
  exact notMem_erase _ _

abbrev CliqueState (G : SimpleGraph V) (C : ↥(tetrahedra G)) :=
  FourState (fun p : ↥C.1 => C.1.erase p.1∈internalTriangles G)

abbrev IncidentClique (G : SimpleGraph V) (T : ↥(internalTriangles G)) :=
  {C : ↥(tetrahedra G) // T.1⊆C.1}

abbrev TriangleLocalState (G : SimpleGraph V) (T : ↥(internalTriangles G)) :=
  TriangleState (IncidentClique G T) ↥T.1

def cliquePort (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(internalTriangles G)) (hTC : T.1⊆C.1) (s : CliqueState G C) : ↥T.1 → Bool :=
  fun j => s.row (opposite G C T hTC) ⟨j.1,hTC j.2⟩

theorem cliquePort_nonconstant (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(internalTriangles G)) (hTC : T.1⊆C.1) (s : CliqueState G C) :
    NonconstantBits (cliquePort G C T hTC s) := by
  let p := opposite G C T hTC
  have hp : C.1.erase p.1∈internalTriangles G := by
    rw [opposite_spec G C T hTC]
    exact T.2
  obtain ⟨⟨j,hjp,hj⟩,⟨k,hkp,hk⟩⟩ := s.nonconstant p hp
  have hjT : j.1∈T.1 := by
    rw [← opposite_spec G C T hTC]
    exact mem_erase.mpr ⟨fun he => hjp (Subtype.ext he),j.2⟩
  have hkT : k.1∈T.1 := by
    rw [← opposite_spec G C T hTC]
    exact mem_erase.mpr ⟨fun he => hkp (Subtype.ext he),k.2⟩
  exact ⟨⟨⟨j.1,hjT⟩,hj⟩,⟨⟨k.1,hkT⟩,hk⟩⟩

theorem cliqueState_extend (G : SimpleGraph V) (C : ↥(tetrahedra G))
    (T : ↥(internalTriangles G)) (hTC : T.1⊆C.1)
    (v : ↥T.1 → Bool) (hv : NonconstantBits v) :
    ∃ s : CliqueState G C,cliquePort G C T hTC s=v := by
  classical
  let p := opposite G C T hTC
  let input : ↥C.1 → Bool := fun j => if hj : j.1∈T.1 then v ⟨j.1,hj⟩ else false
  have hp : C.1.erase p.1∈internalTriangles G := by
    rw [opposite_spec G C T hTC]
    exact T.2
  have hnot := opposite_notMem G C T hTC
  have hin : NonconstantAt input p := by
    obtain ⟨⟨j,hj⟩,⟨k,hk⟩⟩ := hv
    refine ⟨⟨⟨j.1,hTC j.2⟩,?_,?_⟩,⟨⟨k.1,hTC k.2⟩,?_,?_⟩⟩
    · intro he
      exact hnot ((congrArg Subtype.val he) ▸ j.2)
    · simpa only [input,dif_pos j.2] using hj
    · intro he
      exact hnot ((congrArg Subtype.val he) ▸ k.2)
    · simpa only [input,dif_pos k.2] using hk
  have hc : Fintype.card ↥C.1=4 := by
    rw [Fintype.card_coe]
    exact (mem_filter.mp C.2).2.1
  obtain ⟨s,hs⟩ := fourState_extend hc
    (fun q : ↥C.1 => C.1.erase q.1∈internalTriangles G) p hp input hin
  refine ⟨s,?_⟩
  funext j
  have hjp : (⟨j.1,hTC j.2⟩ : ↥C.1)≠p := by
    intro he
    exact hnot ((congrArg Subtype.val he) ▸ j.2)
  change s.row p ⟨j.1,hTC j.2⟩=v j
  rw [hs _ hjp]
  simp only [input,dif_pos j.2]

def incidentCliqueEquiv (G : SimpleGraph V) (T : ↥(internalTriangles G)) :
    IncidentClique G T ≃ ↥((tetrahedra G).filter (fun C => T.1⊆C)) where
  toFun C := ⟨C.1.1,mem_filter.mpr ⟨C.1.2,C.2⟩⟩
  invFun C := ⟨⟨C.1,(mem_filter.mp C.2).1⟩,(mem_filter.mp C.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem incidentClique_card (G : SimpleGraph V) (T : ↥(internalTriangles G)) :
    Fintype.card (IncidentClique G T)=triangleMultiplicity G T.1 := by
  classical
  rw [Fintype.card_congr (incidentCliqueEquiv G T),Fintype.card_coe]
  rfl

theorem incidentClique_card_two_or_three (G : SimpleGraph V) (hG : Admissible G)
    (T : ↥(internalTriangles G)) :
    Fintype.card (IncidentClique G T)=2 ∨ Fintype.card (IncidentClique G T)=3 := by
  obtain ⟨hT,hlo⟩ := mem_internalTriangles.mp T.2
  obtain ⟨hc,hcl⟩ := mem_triangles.mp hT
  have hhi := hG T.1 hc hcl
  rw [incidentClique_card]
  omega

def LocalState (G : SimpleGraph V) : InternalIncidenceNode G → Type _
  | Sum.inl C => CliqueState G C
  | Sum.inr T => TriangleLocalState G T

abbrev PortColor (G : SimpleGraph V) := Option (Σ T : ↥(internalTriangles G),↥T.1 → Bool)

def localPort (G : SimpleGraph V) (x y : InternalIncidenceNode G) :
    LocalState G x → PortColor G :=
  match x,y with
  | Sum.inl C,Sum.inr T => fun s =>
      if hTC : T.1⊆C.1 then some ⟨T,cliquePort G C T hTC s⟩ else none
  | Sum.inr T,Sum.inl C => fun s =>
      if hTC : T.1⊆C.1 then some ⟨T,s.row ⟨C,hTC⟩⟩ else none
  | _,_ => fun _ => none

theorem localState_nonempty (G : SimpleGraph V) (hG : Admissible G)
    (N : InternalIncidenceNode G) : Nonempty (LocalState G N) := by
  classical
  cases N with
  | inl C =>
    exact fourState_nonempty (by
      rw [Fintype.card_coe]
      exact (mem_filter.mp C.2).2.1) _
  | inr T =>
    exact triangleState_nonempty (by
      rw [Fintype.card_coe]
      exact (mem_triangles.mp (mem_internalTriangles.mp T.2).1).1)
      (incidentClique_card_two_or_three G hG T)

theorem localState_matching (G : SimpleGraph V) (hG : Admissible G)
    (x y : InternalIncidenceNode G) (hxy : (internalIncidence G).Adj x y)
    (t : LocalState G y) :
    ∃ s : LocalState G x,localPort G x y s=localPort G y x t := by
  classical
  cases x with
  | inl C =>
    cases y with
    | inl D => exact False.elim hxy
    | inr T =>
      have hTC : T.1⊆C.1 := hxy
      obtain ⟨s,hs⟩ := cliqueState_extend G C T hTC (t.row ⟨C,hTC⟩)
        (t.nonconstant ⟨C,hTC⟩)
      exact ⟨s,by simp only [localPort,dif_pos hTC,hs]⟩
  | inr T =>
    cases y with
    | inr U => exact False.elim hxy
    | inl C =>
      have hTC : T.1⊆C.1 := hxy
      obtain ⟨s,hs⟩ := triangleState_extend (by
        rw [Fintype.card_coe]
        exact (mem_triangles.mp (mem_internalTriangles.mp T.2).1).1)
        (incidentClique_card_two_or_three G hG T) (⟨C,hTC⟩ : IncidentClique G T)
        (cliquePort G C T hTC t) (cliquePort_nonconstant G C T hTC t)
      exact ⟨s,by simp only [localPort,dif_pos hTC,hs]⟩

/-- Actual compatible rows on every clique and every internal triangle,
including the one-dimensional real relation at each triangle. -/
structure CompatibleRows (G : SimpleGraph V) where
  clique : ∀ C : ↥(tetrahedra G),CliqueState G C
  triangle : ∀ T : ↥(internalTriangles G),TriangleLocalState G T
  port_eq : ∀ (C : ↥(tetrahedra G)) (T : ↥(internalTriangles G)) (hTC : T.1⊆C.1),
    cliquePort G C T hTC (clique C)=(triangle T).row ⟨C,hTC⟩

theorem compatibleRows_exists {S : Finset V} {G : SimpleGraph V}
    (h : ThreeTreeOn S G) (hG : Admissible G) : Nonempty (CompatibleRows G) := by
  classical
  obtain ⟨s,hs⟩ := tree_compatible_states (internalIncidence G) h.internalIncidence_isTree
    (LocalState G) (localState_nonempty G hG) (PortColor G) (localPort G)
    (localState_matching G hG)
  refine ⟨{
    clique := fun C => s (Sum.inl C)
    triangle := fun T => s (Sum.inr T)
    port_eq := ?_ }⟩
  intro C T hTC
  have he := hs (Sum.inl C) (Sum.inr T) hTC
  simp only [localPort,dif_pos hTC] at he
  exact sigma_mk_injective (Option.some.inj he)

end ThreeTreeStates
end GraphicalZonotopes
