module

public import Papers.GraphicalZonotopes.Mobius
public import Mathlib.Tactic.Ring

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem zeta_insert (y : SetFunction V) {a : V} {S : Finset V} (ha : a∉S) :
    zeta y (insert a S)=zeta y S+zeta (fun T => y (insert a T)) S := by
  classical
  have hd : Disjoint S.powerset (S.powerset.image (insert a)) := by
    apply disjoint_left.mpr
    intro T hT hi
    obtain ⟨U,hU,rfl⟩ := mem_image.mp hi
    exact ha ((mem_powerset.mp hT) (mem_insert_self _ _))
  have hi : Set.InjOn (insert a) (S.powerset : Set (Finset V)) := by
    intro T hT U hU he
    have haT : a∉T := notMem_mono (mem_powerset.mp hT) ha
    have haU : a∉U := notMem_mono (mem_powerset.mp hU) ha
    have h := congrArg (fun A : Finset V => A.erase a) he
    simpa [haT,haU] using h
  simp only [zeta,powerset_insert]
  rw [sum_union hd,sum_image hi]

/-- The original fourth Möbius coefficient is the complete second difference
of an elemental row on the other two vertices. -/
theorem mobius_four_eq (f : SetFunction V) {a b c d : V}
    (hab : a≠b) (hac : a≠c) (had : a≠d)
    (hbc : b≠c) (hbd : b≠d) (hcd : c≠d) :
    mobius f {a,b,c,d}=
      delta f a b {c,d}-delta f a b {c}-delta f a b {d}+delta f a b ∅ := by
  have h (y : SetFunction V) : y {a,b,c,d}=
      delta (zeta y) a b {c,d}-delta (zeta y) a b {c}-
      delta (zeta y) a b {d}+delta (zeta y) a b ∅ := by
    simp [delta,zeta_insert,hab,hac,had,hbc,hbd,hcd,zeta_empty,zeta_singleton]
    <;> ring
  simpa only [zeta_mobius] using h (mobius f)

/-- Expanded normalized form, convenient for exact lattice certificates. -/
theorem mobius_four_normalized (f : SetFunction V) (hn : TranslationNormalized f)
    {a b c d : V} (hab : a≠b) (hac : a≠c) (had : a≠d)
    (hbc : b≠c) (hbd : b≠d) (hcd : c≠d) :
    mobius f {a,b,c,d}=
      f {a,b,c,d}-f {a,b,c}-f {a,b,d}-f {a,c,d}-f {b,c,d}+
        f {a,b}+f {a,c}+f {a,d}+f {b,c}+f {b,d}+f {c,d} := by
  rw [mobius_four_eq f hab hac had hbc hbd hcd]
  have h0 : f ∅ = 0 := hn.1
  simp only [delta,insert_empty_eq,h0,hn.2]
  ring

end GraphicalZonotopes
