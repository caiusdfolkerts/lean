module

public import TauCeti.LinearAlgebra.ExteriorAlgebra.Contraction
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Span.Defs
public import Lean.Elab.Tactic.Omega

/-!
# The actual Boolean cut complex of a quadratic monomial word

For a word with n internal positions, the mandatory cuts mark its forbidden
adjacent pairs. A valid bar cut set contains every mandatory cut. The
bar differential deletes the optional cuts with their exterior signs.
Creation at any optional position contracts this complex; if all positions
are mandatory, only the top cut degree occurs. The result is an equality
of actual cycles and boundaries, over every commutative coefficient ring.

The later normalized-bar comparison must identify these operators and
these basis vectors with the algebraic bar differential. This file does
not define Koszulness by the combinatorial result.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.MonomialBarCuts

open scoped BigOperators
open CliffordAlgebra

variable {K : Type*} [CommRing K] (n : ℕ)
local notation "V" => Fin n → K
local notation "E" => ExteriorAlgebra K V

noncomputable def coordinateBasis : Module.Basis (Fin n) K V := Pi.basisFun K (Fin n)

def cutPiece (mandatory : Finset (Fin n)) (r : ℕ) : Submodule K E :=
  Submodule.span K {x | ∃ S : Finset (Fin n),mandatory⊆S ∧ S.card=r ∧
    x=(coordinateBasis (K := K) n).ExteriorAlgebra S}

def optionalFunctional (mandatory : Finset (Fin n)) : Module.Dual K V :=
  ∑ i ∈ Finset.univ \ mandatory,(coordinateBasis (K := K) n).coord i

def differential (mandatory : Finset (Fin n)) : E →ₗ[K] E :=
  contractLeft (Q := (0 : QuadraticForm K V)) (optionalFunctional n mandatory)

def insertion (i : Fin n) : E →ₗ[K] E :=
  LinearMap.mulLeft K (ExteriorAlgebra.ι K ((coordinateBasis (K := K) n) i))

theorem optionalFunctional_basis (mandatory : Finset (Fin n)) (i : Fin n) :
    optionalFunctional (K := K) n mandatory ((coordinateBasis (K := K) n) i)=
      if i∈mandatory then 0 else 1 := by
  classical
  simp only [optionalFunctional,LinearMap.sum_apply,Module.Basis.coord_apply,
    Module.Basis.repr_self,Finsupp.single_apply]
  by_cases hi : i∈mandatory
  · rw [if_pos hi]
    apply Finset.sum_eq_zero
    intro j hj
    rw [if_neg]
    intro hji
    subst j
    exact (Finset.mem_sdiff.mp hj).2 hi
  · rw [if_neg hi,Finset.sum_eq_single i]
    · simp only [if_pos rfl,ite_true]
    · intro j hj hji
      exact if_neg hji.symm
    · intro hnot
      exact (hnot (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hi⟩)).elim

theorem differential_basis (mandatory S : Finset (Fin n)) :
    differential (K := K) n mandatory ((coordinateBasis (K := K) n).ExteriorAlgebra S)=
      ∑ i ∈ Finset.univ \ mandatory,
        if i∈S then TauCeti.ExteriorAlgebra.basisEraseSign i S •
          (coordinateBasis (K := K) n).ExteriorAlgebra (S.erase i) else 0 := by
  simp only [differential,optionalFunctional,map_sum,LinearMap.sum_apply,
    TauCeti.ExteriorAlgebra.contractLeft_coord_basis]

set_option maxHeartbeats 1000000 in
theorem differential_squared (mandatory : Finset (Fin n)) (x : E) :
    differential n mandatory (differential n mandatory x)=0 :=
  CliffordAlgebra.contractLeft_contractLeft
    (Q := (0 : QuadraticForm K (Fin n → K)))
    (optionalFunctional (K := K) n mandatory) x

private theorem sign_smul_mem (W : Submodule K E) (ε : ℤˣ) (x : E) (hx : x∈W) : ε • x∈W := by
  rcases Int.units_eq_one_or ε with h | h
  · simpa only [h,one_smul] using hx
  · simpa only [h,Units.smul_def,Units.val_neg,Units.val_one,neg_smul,one_smul]
      using W.neg_mem hx

theorem differential_mem_cutPiece (mandatory : Finset (Fin n)) (r : ℕ)
    (x : E) (hx : x∈cutPiece n mandatory (r+1)) :
    differential n mandatory x∈cutPiece n mandatory r := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨S,hMS,hS,rfl⟩ := hx
      rw [differential_basis]
      apply Submodule.sum_mem
      intro i hi
      by_cases hiS : i∈S
      · rw [if_pos hiS]
        apply sign_smul_mem
        apply Submodule.subset_span
        refine ⟨S.erase i,?_,?_,rfl⟩
        · intro j hj
          exact Finset.mem_erase.mpr
            ⟨fun he => (Finset.mem_sdiff.mp hi).2 (he ▸ hj),hMS hj⟩
        · have hc := Finset.card_erase_add_one hiS
          omega
      · rw [if_neg hiS]
        exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using (cutPiece (K := K) n mandatory r).zero_mem
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using (cutPiece (K := K) n mandatory r).add_mem ihx ihy
  | smul c x hx ih =>
      simpa only [map_smul] using (cutPiece (K := K) n mandatory r).smul_mem c ih

theorem insertion_mem_cutPiece (mandatory : Finset (Fin n)) (i : Fin n) (r : ℕ)
    (x : E) (hx : x∈cutPiece n mandatory r) :
    insertion n i x∈cutPiece n mandatory (r+1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨S,hMS,hS,rfl⟩ := hx
      change ExteriorAlgebra.ι K ((coordinateBasis (K := K) n) i)*
        (coordinateBasis (K := K) n).ExteriorAlgebra S∈_
      rw [TauCeti.ExteriorAlgebra.ι_mul_basis]
      by_cases hi : i∈S
      · rw [if_pos hi]
        exact Submodule.zero_mem _
      · rw [if_neg hi]
        apply sign_smul_mem
        apply Submodule.subset_span
        exact ⟨insert i S,fun j hj => Finset.mem_insert_of_mem (hMS hj),
          by rw [Finset.card_insert_of_notMem hi,hS],rfl⟩
  | zero => simpa only [map_zero] using (cutPiece (K := K) n mandatory (r+1)).zero_mem
  | add x y hx hy ihx ihy =>
      simpa only [map_add] using (cutPiece (K := K) n mandatory (r+1)).add_mem ihx ihy
  | smul c x hx ih =>
      simpa only [map_smul] using (cutPiece (K := K) n mandatory (r+1)).smul_mem c ih

/-- The actual contracting identity retains all required cuts, because
insertion only adjoins one optional position. -/
theorem differential_insertion (mandatory : Finset (Fin n)) (i : Fin n)
    (hi : i∉mandatory) (x : E) :
    differential n mandatory (insertion n i x)+
      insertion n i (differential n mandatory x)=x := by
  change contractLeft (Q := (0 : QuadraticForm K V)) (optionalFunctional n mandatory)
      (ExteriorAlgebra.ι K ((coordinateBasis (K := K) n) i)*x)+
      ExteriorAlgebra.ι K ((coordinateBasis (K := K) n) i)*
        contractLeft (Q := (0 : QuadraticForm K V)) (optionalFunctional n mandatory) x=x
  rw [CliffordAlgebra.contractLeft_ι_mul,optionalFunctional_basis,if_neg hi,
    one_smul,sub_add_cancel]

theorem cutPiece_univ_eq_bot (r : ℕ) (hr : r≠n) :
    cutPiece (K := K) n Finset.univ r=⊥ := by
  apply le_antisymm ?_ bot_le
  apply Submodule.span_le.mpr
  rintro x ⟨S,hS,hcard,rfl⟩
  have he : S=Finset.univ := Finset.eq_univ_of_forall (fun i => hS (Finset.mem_univ i))
  have hn : n=r := by simpa only [he,Finset.card_univ,Fintype.card_fin] using hcard
  exact (hr hn.symm).elim

/-- Every off-top cycle is an actual boundary in the valid-cut subcomplex.
For a word of length n+1, the excluded top is exactly bar degree n+1. -/
theorem off_diagonal_cycle_is_boundary (mandatory : Finset (Fin n))
    (r : ℕ) (hr : r≠n) (x : E) (hx : x∈cutPiece n mandatory r)
    (hdx : differential n mandatory x=0) :
    ∃ y∈cutPiece n mandatory (r+1),differential n mandatory y=x := by
  classical
  by_cases hM : mandatory=Finset.univ
  · rw [hM,cutPiece_univ_eq_bot n r hr,Submodule.mem_bot] at hx
    subst x
    exact ⟨0,Submodule.zero_mem _,map_zero _⟩
  · have hex : ∃ i : Fin n,i∉mandatory := by
      by_contra h
      apply hM
      apply Finset.eq_univ_of_forall
      intro i
      by_contra hi
      exact h ⟨i,hi⟩
    obtain ⟨i,hi⟩ := hex
    refine ⟨insertion n i x,insertion_mem_cutPiece n mandatory i r x hx,?_⟩
    have h := differential_insertion n mandatory i hi x
    rwa [hdx,map_zero,add_zero] at h

end PaperVerification.MonomialBarCuts
