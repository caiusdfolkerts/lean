module

public import Papers.GraphicalZonotopes.TetrahedronRows
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
namespace RootedResponse
variable {W : Type*} [Fintype W]

abbrev NonconstantAt (v : W → Bool) (r : W) : Prop :=
  (∃ j,j≠r ∧ v j=false) ∧ (∃ j,j≠r ∧ v j=true)

/-- Intrinsic local states on the four vertices of a tetrahedron. A face
is indexed by its missing vertex, and a coordinate on that face is indexed
by the third vertex opposite the corresponding edge. -/
structure FourState (internal : W → Prop) where
  row : W → W → Bool
  nonconstant : ∀ i,internal i → NonconstantAt (row i) i
  constant : ∀ i,¬internal i → ∃ b,∀ j,j≠i → row i j=b
  agree : ∀ i j,i≠j → (internal i ∨ internal j) → row i j=row j i

theorem fourState_extend (hcard : Fintype.card W=4) (internal : W → Prop)
    (r : W) (hr : internal r) (v : W → Bool) (hv : NonconstantAt v r) :
    ∃ s : FourState internal,∀ j,j≠r → s.row r j=v j := by
  classical
  let e := Fintype.equivFinOfCardEq hcard
  let I : Finset (Fin 4) := Finset.univ.filter (fun i => internal (e.symm i))
  let input : Fin 4 → Bool := fun i => v (e.symm i)
  have hroot : e r∈I := by simp [I,hr]
  have hin : NonconstantFace input (e r) := by
    obtain ⟨⟨j,hjr,hj⟩,⟨k,hkr,hk⟩⟩ := hv
    exact ⟨⟨e j,(fun he => hjr (e.injective he)),by simpa [input] using hj⟩,
      ⟨e k,(fun he => hkr (e.injective he)),by simpa [input] using hk⟩⟩
  obtain ⟨hport,hnon,hconst,hagree⟩ := relabelledRows_spec I (e r) input hroot hin
  let rows : W → W → Bool := fun i j => relabelledRows I (e r) input (e i) (e j)
  have hnon' : ∀ i,internal i → NonconstantAt (rows i) i := by
    intro i hi
    obtain ⟨⟨j,hji,hj⟩,⟨k,hki,hk⟩⟩ := hnon (e i) (by simp [I,hi])
    refine ⟨⟨e.symm j,?_,?_⟩,⟨e.symm k,?_,?_⟩⟩
    · intro he
      exact hji (by simpa only [Equiv.apply_symm_apply] using congrArg e he)
    · simpa only [rows,Equiv.apply_symm_apply] using hj
    · intro he
      exact hki (by simpa only [Equiv.apply_symm_apply] using congrArg e he)
    · simpa only [rows,Equiv.apply_symm_apply] using hk
  have hconst' : ∀ i,¬internal i → ∃ b,∀ j,j≠i → rows i j=b := by
    intro i hi
    obtain ⟨b,hb⟩ := hconst (e i) (by simp [I,hi])
    exact ⟨b,fun j hji => hb (e j) (fun he => hji (e.injective he))⟩
  have hagree' : ∀ i j,i≠j → (internal i ∨ internal j) → rows i j=rows j i := by
    intro i j hij hi
    apply hagree (e i) (e j) (fun he => hij (e.injective he))
    simpa only [I,Finset.mem_filter,Finset.mem_univ,true_and,
      Equiv.symm_apply_apply] using hi
  refine ⟨⟨rows,hnon',hconst',hagree'⟩,?_⟩
  intro j hjr
  simpa only [rows,input,Equiv.symm_apply_apply] using
    hport (e j) (fun he => hjr (e.injective he))

theorem exists_nonconstantAt (hcard : Fintype.card W=4) (r : W) :
    ∃ v : W → Bool,NonconstantAt v r := by
  classical
  have h := exists_nonconstantFace
  let e := Fintype.equivFinOfCardEq hcard
  obtain ⟨v,⟨⟨j,hjr,hj⟩,⟨k,hkr,hk⟩⟩⟩ := h (e r)
  refine ⟨fun x => v (e x),⟨e.symm j,?_,?_⟩,⟨e.symm k,?_,?_⟩⟩
  · intro he
    exact hjr (by simpa only [Equiv.apply_symm_apply] using congrArg e he)
  · simpa only [Equiv.apply_symm_apply] using hj
  · intro he
    exact hkr (by simpa only [Equiv.apply_symm_apply] using congrArg e he)
  · simpa only [Equiv.apply_symm_apply] using hk

theorem fourState_nonempty (hcard : Fintype.card W=4) (internal : W → Prop) :
    Nonempty (FourState internal) := by
  classical
  by_cases hi : ∃ r,internal r
  · obtain ⟨r,hr⟩ := hi
    obtain ⟨v,hv⟩ := exists_nonconstantAt hcard r
    obtain ⟨s,hs⟩ := fourState_extend hcard internal r hr v hv
    exact ⟨s⟩
  · exact ⟨{
      row := fun _ _ => false
      nonconstant := fun i hi' => False.elim (hi ⟨i,hi'⟩)
      constant := fun _ _ => ⟨false,fun _ _ => rfl⟩
      agree := fun _ _ _ _ => rfl }⟩

end RootedResponse
end GraphicalZonotopes
