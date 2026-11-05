module

public import PaperVerification.ToricParityClasses
public import Mathlib.Topology.Algebra.Group.Basic

@[expose] public section

/-!
# Integral translations in the two mixed assertions

The divisor polytope depends on a torus frame by an integral translation.
These lemmas keep both independent translation vectors, their sum in the
target, and the resulting change of the prescribed parity class explicit.
No choice of frame changes either of the full mixed assertions.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped Pointwise

def translateSet {V : Type*} [Add V] (v : V) (S : Set V) : Set V :=
  (fun x => v+x) '' S

theorem translateSet_add {V : Type*} [AddCommGroup V]
    (v w : V) (S T : Set V) :
    translateSet v S + translateSet w T=translateSet (v+w) (S+T) := by
  ext z
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨x+y,⟨x,hx,y,hy,rfl⟩,by simp only [add_assoc,add_left_comm,add_comm]⟩
  · rintro ⟨_,⟨x,hx,y,hy,rfl⟩,rfl⟩
    exact ⟨v+x,⟨x,hx,rfl⟩,w+y,⟨y,hy,rfl⟩,by simp only [add_assoc,add_left_comm,add_comm]⟩

theorem interior_translateSet {n : ℕ} (v : Ambient n) (S : Set (Ambient n)) :
    interior (translateSet v S)=translateSet v (interior S) :=
  ((Homeomorph.addLeft v).image_interior S).symm

theorem lattice_mem_translateSet_iff {n : ℕ} (v m : Lattice n)
    (S : Set (Ambient n)) :
    embed n m ∈ translateSet (embed n v) S ↔ embed n (m-v)∈S := by
  constructor
  · rintro ⟨x,hx,hxm⟩
    have he : embed n (m-v)=x := by
      rw [map_sub,← hxm]
      exact add_sub_cancel_left (embed n v) x
    simpa only [he] using hx
  · intro hm
    refine ⟨embed n (m-v),hm,?_⟩
    rw [map_sub]
    abel

theorem latticePoints_translateSet {n : ℕ} (v : Lattice n) (S : Set (Ambient n)) :
    {m : Lattice n | embed n m∈translateSet (embed n v) S}=
      translateSet v {m : Lattice n | embed n m∈S} := by
  ext m
  rw [Set.mem_setOf_eq,lattice_mem_translateSet_iff]
  constructor
  · intro hm
    exact ⟨m-v,hm,by abel⟩
  · rintro ⟨z,hz,rfl⟩
    simpa only [add_sub_cancel_left,Set.mem_setOf_eq] using hz

theorem latticePoints_interior_translateSet {n : ℕ}
    (v : Lattice n) (S : Set (Ambient n)) :
    {m : Lattice n | embed n m∈interior (translateSet (embed n v) S)}=
      translateSet v {m : Lattice n | embed n m∈interior S} := by
  rw [interior_translateSet,latticePoints_translateSet]

/-- The first summand's prescribed class changes by precisely the class
of its translation vector, independently of the second translation. -/
theorem prescribedParity_translate {n : ℕ} (P Q : Set (Ambient n))
    (h : ∀ m : Lattice n, embed n m∈interior (P+Q) → ∀ α : ParityClass n,
      ∃ a b : Lattice n,embed n a∈P ∧ embed n b∈Q ∧
        a+b=m ∧ parityClass n a=α)
    (v w : Lattice n) (m : Lattice n)
    (hm : embed n m∈interior
      (translateSet (embed n v) P+translateSet (embed n w) Q))
    (α : ParityClass n) :
    ∃ a b : Lattice n,
      embed n a∈translateSet (embed n v) P ∧
      embed n b∈translateSet (embed n w) Q ∧ a+b=m ∧ parityClass n a=α := by
  have hm' : embed n (m-(v+w))∈interior (P+Q) := by
    rw [translateSet_add,← map_add,interior_translateSet,
      lattice_mem_translateSet_iff] at hm
    exact hm
  obtain ⟨a,b,ha,hb,hab,hα⟩ := h (m-(v+w)) hm' (α-parityClass n v)
  refine ⟨v+a,w+b,?_,?_,?_,?_⟩
  · exact ⟨embed n a,ha,(map_add (embed n) v a).symm⟩
  · exact ⟨embed n b,hb,(map_add (embed n) w b).symm⟩
  · calc
      v+a+(w+b)=(v+w)+(a+b) := by abel
      _=(v+w)+(m-(v+w)) := by rw [hab]
      _=m := by abel
  · rw [map_add,hα]
    abel

/-- The exact adjoint set equality is preserved by independent integral
translations of the two actual polytopes. -/
theorem adjointLatticePoints_translate {n : ℕ} (P Q : Set (Ambient n))
    (h : {m : Lattice n | embed n m∈P}+{m : Lattice n | embed n m∈interior Q}=
      {m : Lattice n | embed n m∈interior (P+Q)}) (v w : Lattice n) :
    {m : Lattice n | embed n m∈translateSet (embed n v) P}+
        {m : Lattice n | embed n m∈interior (translateSet (embed n w) Q)}=
      {m : Lattice n | embed n m∈interior
        (translateSet (embed n v) P+translateSet (embed n w) Q)} := by
  have hsum : translateSet (embed n v) P+translateSet (embed n w) Q=
      translateSet (embed n (v+w)) (P+Q) := by
    rw [translateSet_add,map_add]
  rw [hsum,latticePoints_translateSet,latticePoints_interior_translateSet,
    latticePoints_interior_translateSet,translateSet_add,h]

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.prescribedParity_translate
#print axioms PaperVerification.ToricGeometry.adjointLatticePoints_translate
