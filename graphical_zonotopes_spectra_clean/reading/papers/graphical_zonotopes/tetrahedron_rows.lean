module

public import Papers.GraphicalZonotopes.RootedResponseAlgebra
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 100000
set_option maxRecDepth 4096
namespace GraphicalZonotopes
namespace RootedResponse

/-- Face `i` has coordinates indexed by the other three faces. The entry
at `(i,j)` belongs to their actual common edge. Diagonal entries are unused. -/
abbrev FaceRows := Fin 4 → Fin 4 → Bool

abbrev NonconstantFace (f : Fin 4 → Bool) (i : Fin 4) : Prop :=
  (∃ j,j≠i ∧ f j=false) ∧ (∃ j,j≠i ∧ f j=true)

abbrev ConstantFace (f : Fin 4 → Bool) (i : Fin 4) : Prop :=
  ∃ b,∀ j,j≠i → f j=b

def fourRows (occupied : Finset (Fin 3)) (v : Row) : FaceRows :=
  ![![false,compatibleRows occupied v 0 1,compatibleRows occupied v 0 2,v 0],
    ![compatibleRows occupied v 1 0,false,compatibleRows occupied v 1 2,v 1],
    ![compatibleRows occupied v 2 0,compatibleRows occupied v 2 1,false,v 2],
    ![v 0,v 1,v 2,false]]

abbrev internalFace (occupied : Finset (Fin 3)) (i : Fin 4) : Prop :=
  i=3 ∨ ∃ j : Fin 3,j∈occupied ∧ i=j.castSucc

theorem fourRows_root : ∀ occupied v (i : Fin 3),
    fourRows occupied v 3 i.castSucc=v i := by decide

theorem fourRows_nonconstant : ∀ occupied v,Nonconstant v →
    ∀ i,internalFace occupied i → NonconstantFace (fourRows occupied v i) i := by
  unfold Nonconstant NonconstantFace internalFace
  decide

theorem fourRows_constant : ∀ occupied v i,¬internalFace occupied i →
    ConstantFace (fourRows occupied v i) i := by decide

theorem fourRows_agree : ∀ occupied v i j,i≠j →
    (internalFace occupied i ∨ internalFace occupied j) →
      fourRows occupied v i j=fourRows occupied v j i := by decide

/-- Relabel the root face by a literal permutation. This construction
works for each of the four possible incoming faces; no preferred vertex is
part of the final local-state predicate. -/
def relabelledRows (internal : Finset (Fin 4)) (r : Fin 4)
    (v : Fin 4 → Bool) : FaceRows :=
  let p := Equiv.swap (3 : Fin 4) r
  let occupied := Finset.univ.filter (fun i : Fin 3 => p i.castSucc∈internal)
  let input : Row := fun i => v (p i.castSucc)
  fun i j => fourRows occupied input (p.symm i) (p.symm j)

/-- The finite local extension theorem for one actual tetrahedron. Every
prescribed nonconstant row on any internal face extends to rows on all four
faces. Internal rows remain nonconstant, leaf rows are constant, and every
edge incident with an internal face has matching rows on its two faces. -/
theorem relabelledRows_spec : ∀ internal r v,r∈internal → NonconstantFace v r →
    (∀ j,j≠r → relabelledRows internal r v r j=v j) ∧
    (∀ i,i∈internal → NonconstantFace (relabelledRows internal r v i) i) ∧
    (∀ i,i∉internal → ConstantFace (relabelledRows internal r v i) i) ∧
    (∀ i j,i≠j → (i∈internal ∨ j∈internal) →
      relabelledRows internal r v i j=relabelledRows internal r v j i) := by
  unfold NonconstantFace ConstantFace
  decide

theorem exists_nonconstantFace : ∀ r : Fin 4,∃ v : Fin 4 → Bool,NonconstantFace v r := by decide

end RootedResponse
end GraphicalZonotopes
