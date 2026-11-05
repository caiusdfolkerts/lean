module

public import PaperVerification.EquivariantTowers
public import TauCeti.Algebra.Module.GradedModule.DirectSum
public import TauCeti.Algebra.Module.GradedModule.Shift
public import Mathlib.Tactic.Abel
public import Mathlib.RepresentationTheory.Basic

/-!
# The homogeneous pieces of the complete tower decomposition

The source grading is the actual direct sum of shifted quotient gradings.
Consequently its degree-`p` component is the external direct sum of the
components of degrees `p+j*h`, for all `j : ℕ`. Negative polynomial weights
are used in the hypersurface application, matching the bounded-above grading
in the basis-lifting theorem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped DirectSum

namespace PaperVerification.GradedTowers

variable {K V W : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def sourceGrading (GW : TauCeti.InternalGrading K W) (h : ℕ) :
    TauCeti.InternalGrading K (ℕ →₀ W) := by
  classical
  exact (TauCeti.InternalGrading.directSum fun j : ℕ => GW.shift ((j : ℤ) * h)).map
    (finsuppLequivDFinsupp K : (ℕ →₀ W) ≃ₗ[K] ⨁ _ : ℕ, W).symm

theorem mem_sourceGrading_piece (GW : TauCeti.InternalGrading K W) (h : ℕ)
    (p : ℤ) (x : ℕ →₀ W) :
    x ∈ (sourceGrading GW h).piece p ↔ ∀ j : ℕ, x j ∈ GW.piece (p + (j : ℤ) * h) := by
  classical
  rw [sourceGrading, TauCeti.InternalGrading.mem_map_piece_iff,
    LinearEquiv.symm_symm, TauCeti.InternalGrading.directSum_piece,
    TauCeti.InternalGrading.mem_directSumPiece_iff]
  simp only [TauCeti.InternalGrading.shift_piece]
  rfl

theorem pow_mem (GV : TauCeti.InternalGrading K V) (T : Module.End K V) (h : ℕ)
    (hT : ∀ p x, x ∈ GV.piece p → T x ∈ GV.piece (p - h))
    (j : ℕ) (p : ℤ) (x : V) (hx : x ∈ GV.piece p) :
    (T ^ j) x ∈ GV.piece (p - (j : ℤ) * h) := by
  induction j with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, zero_mul, sub_zero] using hx
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    have ht := hT _ _ ih
    convert ht using 1 <;> simp only [Nat.cast_succ, add_mul, one_mul] <;> abel

theorem extension_isHomogeneous
    (GW : TauCeti.InternalGrading K W) (GV : TauCeti.InternalGrading K V)
    (T : Module.End K V) (s : W →ₗ[K] V) (h : ℕ)
    (hT : ∀ p x, x ∈ GV.piece p → T x ∈ GV.piece (p - h))
    (hs : ∀ p x, x ∈ GW.piece p → s x ∈ GV.piece p) :
    TauCeti.LinearMap.IsHomogeneous (EquivariantTowers.extension T s)
      (sourceGrading GW h).piece GV.piece 0 := by
  classical
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p x hx
  rw [add_zero]
  have hxs := (mem_sourceGrading_piece GW h p x).mp hx
  rw [EquivariantTowers.extension, Finsupp.lsum_apply, Finsupp.sum]
  apply (GV.piece p).sum_mem
  intro j _
  have hp := pow_mem GV T h hT j (p + (j : ℤ) * h) (s (x j))
    (hs _ _ (hxs j))
  simpa only [LinearMap.comp_apply, add_sub_cancel_right] using hp

theorem map_piece_eq_of_homogeneous_equiv
    (GW : TauCeti.InternalGrading K W) (GV : TauCeti.InternalGrading K V)
    (e : W ≃ₗ[K] V)
    (he : TauCeti.LinearMap.IsHomogeneous e.toLinearMap GW.piece GV.piece 0) (p : ℤ) :
    (GW.piece p).map e.toLinearMap = GV.piece p := by
  have hinv := TauCeti.LinearMap.IsHomogeneous.linearEquiv_symm
    (e := e) (G := GW) (H := GV) he
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    simpa only [add_zero] using he.map_mem hx
  · intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    have hy' := hinv.map_mem hy
    rw [add_zero] at hy'
    exact hy'

/-- A degree piece of the tower source is literally the external direct sum
of all the shifted pieces, including zero pieces beyond the degree range. -/
def sourcePieceEquiv (GW : TauCeti.InternalGrading K W) (h : ℕ) (p : ℤ) :
    (⨁ j : ℕ, GW.piece (p + (j : ℤ) * h)) ≃ₗ[K] (sourceGrading GW h).piece p := by
  classical
  let H := fun j : ℕ => GW.shift ((j : ℤ) * h)
  let c := DirectSum.congrLinearEquiv fun j : ℕ =>
    LinearEquiv.ofEq (GW.piece (p + (j : ℤ) * h)) ((H j).piece p)
      (TauCeti.InternalGrading.shift_piece GW ((j : ℤ) * h) p).symm
  let f := (finsuppLequivDFinsupp K : (ℕ →₀ W) ≃ₗ[K] ⨁ _ : ℕ, W).symm
  have hp : (TauCeti.InternalGrading.directSumPiece H p).map f.toLinearMap =
      (sourceGrading GW h).piece p := by
    rw [sourceGrading, TauCeti.InternalGrading.map_piece,
      TauCeti.InternalGrading.directSum_piece]
  exact c.trans ((TauCeti.InternalGrading.directSumPieceEquiv H p).trans
    ((f.submoduleMap _).trans (LinearEquiv.ofEq _ _ hp)))

def componentEquiv
    (GW : TauCeti.InternalGrading K W) (GV : TauCeti.InternalGrading K V)
    (h : ℕ) (e : (ℕ →₀ W) ≃ₗ[K] V)
    (he : TauCeti.LinearMap.IsHomogeneous e.toLinearMap
      (sourceGrading GW h).piece GV.piece 0) (p : ℤ) :
    (⨁ j : ℕ, GW.piece (p + (j : ℤ) * h)) ≃ₗ[K] GV.piece p :=
  (sourcePieceEquiv GW h p).trans ((e.submoduleMap _).trans
    (LinearEquiv.ofEq _ _ (map_piece_eq_of_homogeneous_equiv
      (sourceGrading GW h) GV e he p)))

/-- The underlying Finsupp of the source-piece identification has exactly
its original coordinates, with only the subtype membership forgotten. -/
@[simp] theorem sourcePieceEquiv_apply_apply
    (GW : TauCeti.InternalGrading K W) (h : ℕ) (p : ℤ)
    (x : ⨁ j : ℕ, GW.piece (p + (j : ℤ) * h)) (j : ℕ) :
    (sourcePieceEquiv GW h p x).val j = (x j : W) := by
  classical
  simp only [sourcePieceEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.submoduleMap_apply, finsuppLequivDFinsupp_symm_apply,
    DFinsupp.toFinsupp_coe, TauCeti.InternalGrading.directSumPieceEquiv_apply,
    TauCeti.InternalGrading.directSumPieceInclusion_apply,
    DirectSum.coe_congrLinearEquiv, DirectSum.lmap_apply]
  rfl

section Equivariance

variable {G : Type*} [Monoid G]

/-- The natural restriction of a graded representation to one actual piece. -/
def pieceRepresentation (GW : TauCeti.InternalGrading K W)
    (σ : Representation K G W)
    (hσ : ∀ g p x, x ∈ GW.piece p → σ g x ∈ GW.piece p) (p : ℤ) :
    Representation K G (GW.piece p) :=
  σ.subrepresentation (GW.piece p) (fun g x hx => hσ g p x hx)

/-- The actual direct-sum representation on every shifted homogeneous piece.
The index set is all natural numbers; no bound is imposed on the sum. -/
def shiftedPiecesRepresentation (GW : TauCeti.InternalGrading K W)
    (σ : Representation K G W)
    (hσ : ∀ g p x, x ∈ GW.piece p → σ g x ∈ GW.piece p) (h : ℕ) (p : ℤ) :
    Representation K G (⨁ j : ℕ, GW.piece (p + (j : ℤ) * h)) :=
  Representation.directSum fun j : ℕ => pieceRepresentation GW σ hσ (p + (j : ℤ) * h)

theorem sourceAction_preserves_piece (GW : TauCeti.InternalGrading K W)
    (σ : Representation K G W)
    (hσ : ∀ g p x, x ∈ GW.piece p → σ g x ∈ GW.piece p)
    (h : ℕ) (p : ℤ) (g : G) (x : ℕ →₀ W)
    (hx : x ∈ (sourceGrading GW h).piece p) :
    EquivariantTowers.sourceAction σ g x ∈ (sourceGrading GW h).piece p := by
  rw [mem_sourceGrading_piece] at hx ⊢
  intro j
  change σ g (x j) ∈ GW.piece (p + (j : ℤ) * h)
  exact hσ g _ _ (hx j)

/-- The representation on the actual source-grading submodule. -/
def sourcePieceRepresentation (GW : TauCeti.InternalGrading K W)
    (σ : Representation K G W)
    (hσ : ∀ g p x, x ∈ GW.piece p → σ g x ∈ GW.piece p) (h : ℕ) (p : ℤ) :
    Representation K G ((sourceGrading GW h).piece p) :=
  Representation.subrepresentation (EquivariantTowers.sourceAction σ) ((sourceGrading GW h).piece p)
    (fun g x hx => sourceAction_preserves_piece GW σ hσ h p g x hx)

theorem sourcePieceEquiv_intertwines (GW : TauCeti.InternalGrading K W)
    (σ : Representation K G W)
    (hσ : ∀ g p x, x ∈ GW.piece p → σ g x ∈ GW.piece p)
    (h : ℕ) (p : ℤ) (g : G)
    (x : ⨁ j : ℕ, GW.piece (p + (j : ℤ) * h)) :
    sourcePieceEquiv GW h p (shiftedPiecesRepresentation GW σ hσ h p g x) =
      sourcePieceRepresentation GW σ hσ h p g (sourcePieceEquiv GW h p x) := by
  apply Subtype.ext
  apply Finsupp.ext
  intro j
  change (sourcePieceEquiv GW h p
      (shiftedPiecesRepresentation GW σ hσ h p g x)).val j =
    σ g ((sourcePieceEquiv GW h p x).val j)
  calc
    _ = ((shiftedPiecesRepresentation GW σ hσ h p g x) j : W) :=
      sourcePieceEquiv_apply_apply GW h p _ j
    _ = σ g (x j : W) := rfl
    _ = σ g ((sourcePieceEquiv GW h p x).val j) :=
      congrArg (σ g) (sourcePieceEquiv_apply_apply GW h p x j).symm

/-- Restricting a homogeneous equivariant tower isomorphism gives the genuine
representation isomorphism from the external direct sum of shifted pieces.
The two restricted actions and the external-sum action are all constructed
from the given ambient representations. -/
theorem componentEquiv_intertwines
    (GW : TauCeti.InternalGrading K W) (GV : TauCeti.InternalGrading K V)
    (h : ℕ) (e : (ℕ →₀ W) ≃ₗ[K] V)
    (he : TauCeti.LinearMap.IsHomogeneous e.toLinearMap
      (sourceGrading GW h).piece GV.piece 0)
    (σ : Representation K G W) (ρ : Representation K G V)
    (hσ : ∀ g p x, x ∈ GW.piece p → σ g x ∈ GW.piece p)
    (hρ : ∀ g p x, x ∈ GV.piece p → ρ g x ∈ GV.piece p)
    (hG : ∀ g x, e (EquivariantTowers.sourceAction σ g x) = ρ g (e x))
    (p : ℤ) (g : G) (x : ⨁ j : ℕ, GW.piece (p + (j : ℤ) * h)) :
    componentEquiv GW GV h e he p (shiftedPiecesRepresentation GW σ hσ h p g x) =
      pieceRepresentation GV ρ hρ p g (componentEquiv GW GV h e he p x) := by
  apply Subtype.ext
  change e (sourcePieceEquiv GW h p
      (shiftedPiecesRepresentation GW σ hσ h p g x)).val =
    ρ g (e (sourcePieceEquiv GW h p x).val)
  calc
    _ = e (EquivariantTowers.sourceAction σ g (sourcePieceEquiv GW h p x).val) :=
      congrArg e (congrArg Subtype.val (sourcePieceEquiv_intertwines GW σ hσ h p g x))
    _ = ρ g (e (sourcePieceEquiv GW h p x).val) :=
      hG g (sourcePieceEquiv GW h p x).val

end Equivariance

end PaperVerification.GradedTowers
