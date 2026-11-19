module

public import TauCeti.Algebra.Module.GradedModule.Quotient
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Tactic

/-!
# Hilbert series after quotienting by an injective homogeneous operator

The quotient and every graded piece in this file are actual module quotients
and images of homogeneous submodules.  The proof is rank--nullity applied to
the restriction of the quotient map; homogeneity identifies its kernel.
-/

@[expose] public section
noncomputable section
open scoped BigOperators PowerSeries

namespace PaperVerification.GradedInjectiveQuotient

variable {K S M : Type*} [Field K] [Ring S] [SMul K S]
  [AddCommGroup M] [Module K M] [Module S M] [IsScalarTower K S M]

variable (G : TauCeti.InternalGrading K M ℕ)
  (U : Submodule S M)
  (hU : DirectSum.SetLike.IsHomogeneous G.piece U)

/-- The literal quotient grading, over the original coefficient field. -/
abbrev quotientGrading := G.quotient U hU

/-- The degreewise restriction of the actual quotient map. -/
def quotientPieceMap (d : ℕ) : G.piece d →ₗ[K] (quotientGrading G U hU).piece d :=
  ((U.mkQ.restrictScalars K).domRestrict (G.piece d)).codRestrict _
    (fun x => G.mk_mem_quotient_piece U hU x.property)

@[simp] theorem quotientPieceMap_apply (d : ℕ) (x : G.piece d) :
    (quotientPieceMap G U hU d x : M ⧸ U) = U.mkQ x := rfl

theorem quotientPieceMap_surjective (d : ℕ) :
    Function.Surjective (quotientPieceMap G U hU d) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := (G.mem_quotient_piece_iff U hU).mp y.property
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

instance quotientPiece_finite (d : ℕ) [FiniteDimensional K (G.piece d)] :
    FiniteDimensional K ((quotientGrading G U hU).piece d) :=
  Module.Finite.of_surjective (quotientPieceMap G U hU d)
    (quotientPieceMap_surjective G U hU d)

variable (T : M →ₗ[K] M) (e : ℕ)
  (hT : TauCeti.LinearMap.IsHomogeneous T G.piece G.piece e)

include hT

/-- Multiplication or another homogeneous operator restricted to one piece. -/
def operatorPieceMap (d : ℕ) : G.piece d →ₗ[K] G.piece (d+e) :=
  (T.domRestrict (G.piece d)).codRestrict _ (fun x => hT.map_mem x.property)

@[simp] theorem operatorPieceMap_apply (d : ℕ) (x : G.piece d) :
    (operatorPieceMap G T e hT d x : M) = T x := rfl

theorem operatorPieceMap_injective (hinj : Function.Injective T) (d : ℕ) :
    Function.Injective (operatorPieceMap G T e hT d) := by
  intro x y h
  exact Subtype.ext (hinj (congrArg Subtype.val h))

theorem quotientPieceMap_ker
    (hUT : U.restrictScalars K = LinearMap.range T) (d : ℕ) :
    LinearMap.ker (quotientPieceMap G U hU (d+e)) =
      LinearMap.range (operatorPieceMap G T e hT d) := by
  ext x
  constructor
  · intro hx
    have hxU : (x : M) ∈ U := by
      apply (Submodule.Quotient.mk_eq_zero U).mp
      exact congrArg Subtype.val hx
    have hxrange : (x : M) ∈ LinearMap.range T := hUT ▸ hxU
    obtain ⟨y, hy⟩ := hxrange
    refine ⟨DirectSum.decompose G.piece y d, Subtype.ext ?_⟩
    change T (DirectSum.decompose G.piece y d : M) = (x : M)
    rw [hT.map_decompose, hy]
    exact DirectSum.decompose_of_mem_same G.piece x.property
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    change U.mkQ (T y) = 0
    apply (Submodule.Quotient.mk_eq_zero U).mpr
    have hx : T y ∈ LinearMap.range T := ⟨y, rfl⟩
    change T y ∈ U.restrictScalars K
    rw [hUT]
    exact hx

theorem image_projection_below_degree (d : ℕ) (hde : d < e) (x : M) :
    (DirectSum.decompose G.piece (T x) d : M) = 0 := by
  induction x using DirectSum.Decomposition.inductionOn G.piece with
  | zero => simp
  | @homogeneous j x =>
      exact DirectSum.decompose_of_mem_ne G.piece (hT.map_mem x.property) (by omega)
  | add x y hx hy =>
      simpa only [map_add, DirectSum.decompose_add, DirectSum.add_apply,
        Submodule.coe_add, hx, hy, add_zero]

theorem quotientPieceMap_ker_below
    (hUT : U.restrictScalars K = LinearMap.range T) (d : ℕ) (hde : d < e) :
    LinearMap.ker (quotientPieceMap G U hU d) = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hxU : (x : M) ∈ U :=
      (Submodule.Quotient.mk_eq_zero U).mp (congrArg Subtype.val hx)
    have hxrange : (x : M) ∈ LinearMap.range T := hUT ▸ hxU
    obtain ⟨y, hy⟩ := hxrange
    have hzero := image_projection_below_degree G T e hT d hde y
    rw [hy, DirectSum.decompose_of_mem_same G.piece x.property] at hzero
    exact Subtype.ext hzero
  · exact bot_le

theorem finrank_quotient_piece_add
    (hinj : Function.Injective T)
    (hUT : U.restrictScalars K = LinearMap.range T) (d : ℕ)
    [FiniteDimensional K (G.piece (d+e))] :
    Module.finrank K ((quotientGrading G U hU).piece (d+e)) +
      Module.finrank K (G.piece d) = Module.finrank K (G.piece (d+e)) := by
  have h := (quotientPieceMap G U hU (d+e)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (quotientPieceMap_surjective G U hU (d+e)),
    finrank_top, quotientPieceMap_ker G U hU T e hT hUT d,
    LinearMap.finrank_range_of_inj (operatorPieceMap_injective G T e hT hinj d)] at h
  exact h

theorem finrank_quotient_piece_below
    (hUT : U.restrictScalars K = LinearMap.range T) (d : ℕ) (hde : d < e)
    [FiniteDimensional K (G.piece d)] :
    Module.finrank K ((quotientGrading G U hU).piece d) =
      Module.finrank K (G.piece d) := by
  have h := (quotientPieceMap G U hU d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (quotientPieceMap_surjective G U hU d),
    finrank_top, quotientPieceMap_ker_below G U hU T e hT hUT d hde,
    finrank_bot, add_zero] at h
  exact h

/-- The Hilbert series of the literal internally graded module. -/
def hilbertSeries (G : TauCeti.InternalGrading K M ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk (fun d => (Module.finrank K (G.piece d) : ℤ))

theorem hilbertSeries_quotient
    (hinj : Function.Injective T)
    (hUT : U.restrictScalars K = LinearMap.range T)
    (hfinite : ∀ d, FiniteDimensional K (G.piece d)) :
    hilbertSeries (quotientGrading G U hU) =
      hilbertSeries G * (1-PowerSeries.X^e) := by
  apply PowerSeries.ext
  intro d
  letI := hfinite d
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow']
  simp only [hilbertSeries, PowerSeries.coeff_mk]
  split_ifs with hed
  · letI := hfinite (d-e+e)
    have h := finrank_quotient_piece_add G U hU T e hT hinj hUT (d-e)
    rw [Nat.sub_add_cancel hed] at h
    have hz : (Module.finrank K ((quotientGrading G U hU).piece d) : ℤ) +
        (Module.finrank K (G.piece (d-e)) : ℤ) =
        (Module.finrank K (G.piece d) : ℤ) := by exact_mod_cast h
    omega
  · simpa only [sub_zero] using congrArg (fun n : ℕ => (n : ℤ))
      (finrank_quotient_piece_below G U hU T e hT hUT d (by omega))

end PaperVerification.GradedInjectiveQuotient
