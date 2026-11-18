module

public import sunlet.generic_pair_geometry
public import sunlet.contact_development
public import Mathlib.Data.ZMod.Basic

/-!
# The five observed cyclic colors

The actual colors are1,2,−1,3,−2. Every support property used in the
sparse Hessian theorem is proved uniformly for all m≥6.
-/

@[expose] public section
noncomputable section

namespace Sunlet.CyclicSparseWitness

open ToricDifferential ToricPairAlgebra

def colorNat (m : ℕ) : Fin 5 → ℕ := ![1, 2, m-1, 3, m-2]
def shift (m : ℕ) (a : Fin 5) : ZMod m := (colorNat m a : ℕ)
def permutation (m : ℕ) (a : Fin 5) : Equiv.Perm (ZMod m) :=
  Equiv.addLeft (shift m a)
def firstSupport : Finset (Fin 5) := {0,1}
def secondSupport : Finset (Fin 5) := {2,3,4}

variable (m : ℕ) (hm : 6 ≤ m)

include hm

theorem color_bounds (a : Fin 5) : 0 < colorNat m a ∧ colorNat m a < m := by
  fin_cases a <;> simp [colorNat] <;> omega

theorem colorNat_injective : Function.Injective (colorNat m) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [colorNat] at h ⊢ <;> omega

theorem shift_injective : Function.Injective (shift m) := by
  intro a b h
  apply colorNat_injective m hm
  have hv := congrArg ZMod.val h
  simpa only [shift, ZMod.val_natCast_of_lt (color_bounds m hm a).2,
    ZMod.val_natCast_of_lt (color_bounds m hm b).2] using hv

theorem shift_ne_zero (a : Fin 5) : shift m a ≠ 0 := by
  intro h
  have hh := congrArg ZMod.val h
  have hz : colorNat m a = 0 := by
    simpa only [shift, ZMod.val_natCast_of_lt (color_bounds m hm a).2,
      ZMod.val_zero] using hh
  have := (color_bounds m hm a).1
  omega

omit hm in
@[simp] theorem shift_zero : shift m 0 = 1 := by simp [shift,colorNat]
omit hm in
@[simp] theorem shift_one : shift m 1 = 2 := by simp [shift,colorNat]
@[simp] theorem shift_two : shift m 2 = -1 := by
  simp [shift,colorNat,Nat.cast_sub (by omega : 1 ≤ m),ZMod.natCast_self]
omit hm in
@[simp] theorem shift_three : shift m 3 = 3 := by simp [shift,colorNat]
@[simp] theorem shift_four : shift m 4 = -2 := by
  simp [shift,colorNat,Nat.cast_sub (by omega : 2 ≤ m),ZMod.natCast_self]

theorem permutation_ne {a b : Fin 5} (hab : a ≠ b) :
    permutation m a ≠ permutation m b := by
  intro h
  apply hab
  apply shift_injective m hm
  simpa [permutation] using congrArg (fun p : Equiv.Perm (ZMod m) => p 0) h

theorem derangement (a : Fin 5) (x : ZMod m) : permutation m a x ≠ x := by
  intro h
  apply shift_ne_zero m hm a
  apply add_right_cancel (b := x)
  simpa [permutation] using h

theorem outgoing_injective : Function.Injective (fun a => permutation m a 0) := by
  simpa [permutation] using shift_injective m hm

theorem incoming_injective : Function.Injective (fun a => (permutation m a).symm 0) := by
  intro a b h
  apply shift_injective m hm
  have hh := congrArg Neg.neg h
  simpa [permutation] using hh

omit hm in
lemma color_edge [NeZero m] {P : Set (Fin 5)} {a : Fin 5} (ha : a ∈ P) (x : ZMod m) :
    ColorConnected (permutation m) P x (shift m a + x) :=
  Relation.EqvGen.rel _ _ ⟨a,ha,rfl⟩

omit hm in
theorem transitive_of_step_one [NeZero m] (P : Set (Fin 5))
    (hstep : ∀ x : ZMod m, ColorConnected (permutation m) P x (1+x)) :
    TransitiveFamily (permutation m) P := by
  have hn (n : ℕ) (x : ZMod m) : ColorConnected (permutation m) P x (n+x) := by
    induction n with
    | zero => simpa only [Nat.cast_zero,zero_add,Sunlet.ColorConnected] using
        Relation.EqvGen.refl (r := ColorEdge (permutation m) P) x
    | succ n ih =>
      have hh := Relation.EqvGen.trans _ _ _ ih (hstep (n+x))
      simpa only [Sunlet.ColorConnected,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using hh
  intro x y
  have hh := hn (y-x).val x
  simpa only [ZMod.natCast_zmod_val,sub_add_cancel] using hh

omit hm in
theorem transitive_of_plus_one [NeZero m] (P : Set (Fin 5)) (h0 : (0 : Fin 5) ∈ P) :
    TransitiveFamily (permutation m) P :=
  transitive_of_step_one m P (by intro x; simpa using color_edge m h0 x)

theorem transitive_of_minus_one [NeZero m] (P : Set (Fin 5)) (h2 : (2 : Fin 5) ∈ P) :
    TransitiveFamily (permutation m) P :=
  transitive_of_step_one m P (by
    intro x
    have hh := Relation.EqvGen.symm _ _ (color_edge m h2 (1+x))
    simpa only [Sunlet.ColorConnected,shift_two m hm,neg_add_cancel_left] using hh)

theorem transitive_of_three_minus_two [NeZero m] (P : Set (Fin 5))
    (h3 : (3 : Fin 5) ∈ P) (h4 : (4 : Fin 5) ∈ P) :
    TransitiveFamily (permutation m) P :=
  transitive_of_step_one m P (by
    intro x
    have hh := Relation.EqvGen.trans _ _ _ (color_edge m h3 x)
      (color_edge m h4 (shift m 3+x))
    unfold Sunlet.ColorConnected
    convert hh using 1 <;> simp only [shift_three,shift_four m hm] <;> ring)

omit hm in
theorem first_transitive [NeZero m] :
    TransitiveFamily (permutation m) (firstSupport : Set (Fin 5)) :=
  transitive_of_plus_one m _ (by simp [firstSupport])

theorem second_transitive [NeZero m] :
    TransitiveFamily (permutation m) (secondSupport : Set (Fin 5)) :=
  transitive_of_minus_one m hm _ (by simp [secondSupport])

theorem deletion_transitive [NeZero m] (b : Fin 5) (hb : b ∈ secondSupport) :
    TransitiveFamily (permutation m) ((secondSupport : Set (Fin 5)) \ {b}) := by
  fin_cases b
  · simp [secondSupport] at hb
  · simp [secondSupport] at hb
  · exact transitive_of_three_minus_two m hm _ (by simp [secondSupport]) (by simp [secondSupport])
  · exact transitive_of_minus_one m hm _ (by simp [secondSupport])
  · exact transitive_of_minus_one m hm _ (by simp [secondSupport])

def positiveVertex (n : ℕ) (hn : 0 < n) (hnm : n < m) : {x : ZMod m // x ≠ 0} :=
  ⟨(n : ZMod m), by
    intro h
    have hh := congrArg ZMod.val h
    simp only [ZMod.val_natCast_of_lt hnm,ZMod.val_zero] at hh
    omega⟩

/-- Deleting zero from the−1cycle leaves the path1,2,…,m−1. -/
theorem ordinary_connected [NeZero m] :
    ∀ x y, Relation.EqvGen
      (PuncturedBothEndpoints.OrdinaryEdge (0 : ZMod m) (permutation m)
        (secondSupport : Set (Fin 5))) x y := by
  let R := PuncturedBothEndpoints.OrdinaryEdge (0 : ZMod m) (permutation m)
    (secondSupport : Set (Fin 5))
  let one := positiveVertex m 1 (by omega) (by omega)
  have hpath (n : ℕ) (hn : n+1 < m) :
      Relation.EqvGen R one (positiveVertex m (n+1) (by omega) hn) := by
    induction n with
    | zero => exact Relation.EqvGen.refl _
    | succ n ih =>
      have he : R (positiveVertex m (n+2) (by omega) hn)
          (positiveVertex m (n+1) (by omega) (by omega)) := by
        refine ⟨2,by simp [secondSupport],?_⟩
        change shift m 2 + (n+2 : ℕ) = (n+1 : ℕ)
        rw [shift_two m hm]
        push_cast
        ring
      exact Relation.EqvGen.trans _ _ _ (ih (by omega)) (Relation.EqvGen.symm _ _
        (Relation.EqvGen.rel _ _ he))
  have hx (x : {x : ZMod m // x ≠ 0}) : Relation.EqvGen R one x := by
    have hpos : 0 < x.val.val := ZMod.val_pos.mpr x.property
    have hlt := x.val.val_lt
    have hh := hpath (x.val.val-1) (by omega)
    convert hh using 1
    apply Subtype.ext
    change x.val = ((x.val.val-1+1 : ℕ) : ZMod m)
    rw [Nat.sub_add_cancel (by omega),ZMod.natCast_zmod_val]
  intro x y
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hx x)) (hx y)

def witness {k : Type*} [Field k] [CharZero k] [NeZero m] :
    SparseWitness (k := k) (0 : ZMod m) (permutation m) where
  A := firstSupport
  B := secondSupport
  disjoint := by
    apply Set.disjoint_left.mpr
    intro a ha hb
    fin_cases a <;> simp_all [firstSupport,secondSupport]
  Atwo := ⟨0,by simp [firstSupport],1,by simp [firstSupport],
    permutation_ne m hm (by decide)⟩
  Btwo := ⟨2,by simp [secondSupport],3,by simp [secondSupport],
    permutation_ne m hm (by decide)⟩
  Atrans := first_transitive m
  Btrans := second_transitive m hm
  radial := by
    apply SparseContact.radial (permutation m) 0 (firstSupport : Set (Fin 5))
      (secondSupport : Set (Fin 5)) (by
        apply Set.disjoint_left.mpr
        intro a ha hb
        fin_cases a <;> simp_all [firstSupport,secondSupport])
      (by simpa only [ZMod.card] using (show 5 ≤ m by omega)) (derangement m hm)
      ⟨0,by simp [firstSupport]⟩
      ⟨2,by simp [secondSupport],3,by simp [secondSupport],permutation_ne m hm (by decide)⟩
      (second_transitive m hm)
    · intro b hb
      fin_cases b
      · simp [secondSupport] at hb
      · simp [secondSupport] at hb
      · exact ⟨3,by simp [secondSupport],4,by simp [secondSupport],permutation_ne m hm (by decide)⟩
      · exact ⟨2,by simp [secondSupport],4,by simp [secondSupport],permutation_ne m hm (by decide)⟩
      · exact ⟨2,by simp [secondSupport],3,by simp [secondSupport],permutation_ne m hm (by decide)⟩
    · exact deletion_transitive m hm
    · exact ⟨2,by simp [secondSupport],3,by simp [secondSupport],4,by simp [secondSupport],
        permutation_ne m hm (by decide),permutation_ne m hm (by decide),
        permutation_ne m hm (by decide)⟩
    · exact ordinary_connected m hm
    · exact outgoing_injective m hm
    · exact incoming_injective m hm

end Sunlet.CyclicSparseWitness
