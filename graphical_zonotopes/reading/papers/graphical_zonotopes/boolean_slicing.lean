module

public import Papers.GraphicalZonotopes.BooleanSliceIntersection
public import Papers.GraphicalZonotopes.DoubledPhase

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes
namespace BooleanFourier
open Finset
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev DeletedIndex (a : I) := {i : I // i≠a}

def extendCube (a : I) (b : Bool) (v : Cube (DeletedIndex a)) : Cube I :=
  fun i => if h : i=a then b else v ⟨i,h⟩

@[simp] theorem extendCube_at (a : I) (b : Bool) (v : Cube (DeletedIndex a)) :
    extendCube a b v a=b := by simp [extendCube]

@[simp] theorem extendCube_other (a : I) (b : Bool) (v : Cube (DeletedIndex a))
    (i : DeletedIndex a) : extendCube a b v i=v i := by simp [extendCube,i.2]

theorem prod_split_deleted (a : I) (f : I → ℝ) :
    (∏ i,f i)=f a*∏ i : DeletedIndex a,f i := by
  rw [← mul_prod_erase univ f (mem_univ a)]
  rw [prod_subtype (p := fun i : I => i≠a) (univ.erase a) (by simp) f]

def deletedSet (a : I) (L : Finset I) : Finset (DeletedIndex a) :=
  univ.filter fun i => i.1∈L

@[simp] theorem mem_deletedSet (a : I) (L : Finset I) (i : DeletedIndex a) :
    i∈deletedSet a L ↔ i.1∈L := by simp [deletedSet]

@[simp] theorem deletedSet_univ (a : I) : deletedSet a univ=univ := by
  ext i
  simp

theorem character_extendCube (a : I) (b : Bool) (v : Cube (DeletedIndex a)) (L : Finset I) :
    character L (extendCube a b v)=
      (if a∈L then spin b else 1)*character (deletedSet a L) v := by
  unfold character
  rw [prod_split_deleted a]
  simp only [extendCube_at,extendCube_other,mem_deletedSet]

theorem trueSet_extendCube_false (a : I) (v : Cube (DeletedIndex a)) :
    trueSet (extendCube a false v)=(trueSet v).map (Function.Embedding.subtype _) := by
  ext i
  by_cases hi : i=a
  · subst i
    simp [trueSet]
  · simp only [trueSet,mem_filter,mem_univ,true_and,mem_map]
    constructor
    · intro h
      exact ⟨⟨i,hi⟩,by simpa [extendCube,hi] using h,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      simpa using hj

theorem trueSet_extendCube_true (a : I) (v : Cube (DeletedIndex a)) :
    trueSet (extendCube a true v)=insert a ((trueSet v).map (Function.Embedding.subtype _)) := by
  ext i
  by_cases hi : i=a
  · subst i
    simp [trueSet]
  · simp only [trueSet,mem_filter,mem_univ,true_and,mem_insert,hi,false_or,mem_map]
    constructor
    · intro h
      exact ⟨⟨i,hi⟩,by simpa [extendCube,hi] using h,rfl⟩
    · rintro ⟨j,hj,rfl⟩
      simpa using hj

@[simp] theorem trueSet_extendCube_false_card (a : I) (v : Cube (DeletedIndex a)) :
    (trueSet (extendCube a false v)).card=(trueSet v).card := by
  rw [trueSet_extendCube_false,card_map]

@[simp] theorem trueSet_extendCube_true_card (a : I) (v : Cube (DeletedIndex a)) :
    (trueSet (extendCube a true v)).card=(trueSet v).card+1 := by
  rw [trueSet_extendCube_true,card_insert_of_notMem,card_map]
  simp

theorem completePhase_extendCube_false (a : I) (c : ℝ) (L : Finset I)
    (v : Cube (DeletedIndex a)) :
    completePhase c L (extendCube a false v)=completePhase c (deletedSet a L) v := by
  simp [completePhase,character_extendCube,spin]

theorem completePhase_extendCube_true (a : I) (c : ℝ) (L : Finset I)
    (v : Cube (DeletedIndex a)) :
    completePhase c L (extendCube a true v)=
      (if a∈L then -1 else 1)*character univ v*completePhase c (deletedSet a L) v := by
  simp only [completePhase,trueSet_extendCube_true_card,character_extendCube,spin,ite_true]
  have hp : (-1 : ℝ)^((trueSet v).card+1).choose 2=
      (-1 : ℝ)^((trueSet v).card.choose 2)*(-1 : ℝ)^((trueSet v).card) := by
    simpa [QuadraticSign.triangle,QuadraticSign.parity] using
      QuadraticSign.triangle_succ (trueSet v).card
  rw [hp,DoubledParts.character_univ_parity]
  change _=(if a∈L then -1 else 1)*(-1 : ℝ)^((trueSet v).card)*_
  ring

def slicePhase (a : I) (c : ℝ) (L : Finset I) (b : Bool) : Cube (DeletedIndex a) → ℝ :=
  if b then completePhase (-(if a∈L then -1 else 1)*c) (deletedSet a L)ᶜ
  else completePhase c (deletedSet a L)

/-- Fixing the two original signs of a deleted part to `(b, false)` fixes
both transformed bits to `b`; its two actual slices are again Boolean faces. -/
theorem faceFunction_slice (a : I) (c : ℝ) (L : Finset I) (b : Bool)
    (uv : Cube (DeletedIndex a) × Cube (DeletedIndex a)) :
    faceFunction (completePhase c L)
        (extendCube a b uv.1,extendCube a b uv.2)=faceFunction (slicePhase a c L b) uv := by
  cases b
  · simp [faceFunction,phase,character_extendCube,completePhase_extendCube_false,slicePhase,spin]
  · rw [faceFunction,phase,character_extendCube,deletedSet_univ,
      completePhase_extendCube_true]
    simp only [mem_univ,ite_true,spin]
    rw [faceFunction,phase]
    simp only [slicePhase,ite_true]
    simp only [completePhase]
    rw [← character_compl]
    ring

theorem slicePhase_isSign (a : I) {c : ℝ} (hc : c=1 ∨ c= -1) (L : Finset I)
    (b : Bool) (v : Cube (DeletedIndex a)) :
    slicePhase a c L b v=1 ∨ slicePhase a c L b v= -1 := by
  cases b
  · exact completePhase_isSign hc _ _
  · apply completePhase_isSign
    rcases hc with rfl | rfl <;> split_ifs <;> norm_num

theorem slicePhase_nonseparable (a : I) {c : ℝ} (hc : c≠0) (L : Finset I) (b : Bool) :
    Nonseparable (slicePhase a c L b) := by
  cases b
  · exact completePhase_nonseparable hc _
  · apply completePhase_nonseparable
    apply mul_ne_zero _ hc
    split_ifs <;> norm_num

theorem slicePhase_distinct (a : I) [Nonempty (DeletedIndex a)] {c : ℝ}
    (hc : c≠0) (L : Finset I) : slicePhase a c L false≠slicePhase a c L true := by
  have he : slicePhase a c L true=(fun v =>
      -(if a∈L then -1 else 1)*character univ v*completePhase c (deletedSet a L) v) := by
    funext v
    simp only [slicePhase,ite_true]
    simp only [completePhase]
    rw [← character_compl]
    ring
  rw [he]
  exact ne_parity_multiple (completePhase_ne_zero hc _) _

/-- Evaluation at arbitrary fixed values of the removed transformed bits
preserves the exact tensor space on the remaining coordinates. -/
theorem tensorSpace_slice (a : I) (b c : Bool) {p : (Cube I × Cube I) → ℝ}
    (hp : p∈tensorSpace) :
    (fun uv : Cube (DeletedIndex a) × Cube (DeletedIndex a) =>
      p (extendCube a b uv.1,extendCube a c uv.2))∈tensorSpace := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨s,rfl⟩ := hp
    let k : ℝ := match s a with
      | none => 1
      | some false => spin b
      | some true => spin b*spin c
    have ht : tensorMonomial (fun i : DeletedIndex a => s i)∈tensorSpace :=
      Submodule.subset_span ⟨_,rfl⟩
    convert (tensorSpace (I := DeletedIndex a)).smul_mem k ht using 1
    funext uv
    simp only [tensorMonomial,Pi.smul_apply,smul_eq_mul]
    rw [prod_split_deleted a]
    simp only [extendCube_at,extendCube_other]
    rfl
  | zero =>
    exact (tensorSpace (I := DeletedIndex a)).zero_mem
  | add p q hp hq ihp ihq =>
    exact (tensorSpace (I := DeletedIndex a)).add_mem ihp ihq
  | smul r p hp ih =>
    exact (tensorSpace (I := DeletedIndex a)).smul_mem r ih

end BooleanFourier
end GraphicalZonotopes
