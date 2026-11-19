module

public import PaperVerification.AlternatingFormsOddActualOrbit
public import PaperVerification.AlternatingFormsOddAbstractBasis
import Lean.Elab.Tactic.Omega

/-!
# The odd orbit normal form is the literal interleaved path pencil

The orbit calculation groups the `a` and `b` coordinates in two blocks.
The exterior straightening theorem interleaves them.  This file gives
the explicit permutation, identifies both quadratic generators including
their signs, and transports the complete good-monomial basis to the
actual orbit normal form in every exterior degree.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {K : Type*} [Field K]

/-- `aᵢ` occupies the odd position `2i+1` and `bⱼ` the even position `2j`. -/
def oddOrbitInterleave (t : ℕ) : OddOrbitMode t ≃ Fin (2*(t+1)+1) where
  toFun
    | .inl i => ⟨2*i.val+1, by have := i.isLt; omega⟩
    | .inr j => ⟨2*j.val, by have := j.isLt; omega⟩
  invFun j := if h : j.val%2=0 then .inr ⟨j.val/2, by have := j.isLt; omega⟩
    else .inl ⟨j.val/2, by have := j.isLt; omega⟩
  left_inv i := by
    cases i with
    | inl i =>
        have he : ¬(2*i.val+1)%2=0 := by omega
        simp only [he, dite_false, Sum.inl.injEq]
        apply Fin.ext
        dsimp only
        omega
    | inr j =>
        have he : (2*j.val)%2=0 := by omega
        simp only [he, dite_true, Sum.inr.injEq]
        apply Fin.ext
        dsimp only
        omega
  right_inv j := by
    dsimp only
    split_ifs <;> apply Fin.ext <;> dsimp only <;> omega

def oddOrbitInterleavedBasis (t : ℕ) :
    Module.Basis (Fin (2*(t+1)+1)) K (OddOrbitMode t → K) :=
  (Pi.basisFun K (OddOrbitMode t)).reindex (oddOrbitInterleave t)

theorem oddOrbitInterleavedBasis_at (t : ℕ) (i : OddOrbitMode t) :
    oddOrbitInterleavedBasis (K := K) t (oddOrbitInterleave t i) =
      Pi.basisFun K (OddOrbitMode t) i := by
  simp only [oddOrbitInterleavedBasis, Module.Basis.reindex_apply,
    Equiv.symm_apply_apply]

theorem oddOrbitInterleavedBasis_middle (t : ℕ) (i : Fin (t+1)) :
    oddOrbitInterleavedBasis (K := K) t (oddPathMiddle i) =
      Pi.basisFun K (OddOrbitMode t) (Sum.inl i) := by
  exact oddOrbitInterleavedBasis_at t (Sum.inl i)

theorem oddOrbitInterleavedBasis_first (t : ℕ) (i : Fin (t+1)) :
    oddOrbitInterleavedBasis (K := K) t (oddPathFirstLeft i) =
      Pi.basisFun K (OddOrbitMode t) (Sum.inr i.castSucc) := by
  exact oddOrbitInterleavedBasis_at t (Sum.inr i.castSucc)

theorem oddOrbitInterleavedBasis_second (t : ℕ) (i : Fin (t+1)) :
    oddOrbitInterleavedBasis (K := K) t (oddPathSecondRight i) =
      Pi.basisFun K (OddOrbitMode t) (Sum.inr i.succ) := by
  exact oddOrbitInterleavedBasis_at t (Sum.inr i.succ)

theorem exteriorPair_swap {M : Type*} [AddCommGroup M] [Module K M] (u v : M) :
    exteriorPair (K := K) u v = -exteriorPair v u := by
  apply Subtype.ext
  simp only [exteriorPair_coe, Submodule.coe_neg]
  exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u v)

/-- The first orbit generator is exactly the second path generator. -/
theorem oddOrbitFirstForm_eq_path (t : ℕ) :
    oddOrbitFirstForm (K := K) t =
      oddPathSecondQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t) := by
  simp only [oddOrbitFirstForm, orbitIncidenceForm, oddPathSecondQuadratic,
    matchingQuadratic, oddOrbitInterleavedBasis_middle,
    oddOrbitInterleavedBasis_second, exteriorPair]

/-- The second orbit generator is minus the first path generator.  The
sign is retained explicitly before comparing the generated ideals. -/
theorem oddOrbitSecondForm_eq_path (t : ℕ) :
    oddOrbitSecondForm (K := K) t =
      -oddPathFirstQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t) := by
  simp only [oddOrbitSecondForm, orbitIncidenceForm, oddPathFirstQuadratic,
    matchingQuadratic, oddOrbitInterleavedBasis_first,
    oddOrbitInterleavedBasis_middle, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact exteriorPair_swap _ _

theorem quadraticSpan_swap_neg {M : Type*} [AddCommGroup M] [Module K M]
    (f g : ⋀[K]^2 M) :
    Submodule.span K ({f,g} : Set (⋀[K]^2 M)) =
      Submodule.span K ({g,-f} : Set (⋀[K]^2 M)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      have hn : -f ∈ Submodule.span K ({g,-f} : Set (⋀[K]^2 M)) :=
        Submodule.subset_span (by simp)
      change f ∈ Submodule.span K ({g,-f} : Set (⋀[K]^2 M))
      have hnn := (Submodule.span K ({g,-f} : Set (⋀[K]^2 M))).neg_mem hn
      rw [neg_neg] at hnn
      exact hnn
    · rw [hx]
      exact Submodule.subset_span (by simp)
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact Submodule.subset_span (by simp)
    · rw [hx]
      exact Submodule.neg_mem _ (Submodule.subset_span (by simp))

theorem oddOrbit_quadraticSpan (t : ℕ) :
    Submodule.span K
      ({oddPathFirstQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t),
        oddPathSecondQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t)} :
          Set (⋀[K]^2 (OddOrbitMode t → K))) =
      Submodule.span K ({oddOrbitFirstForm (K := K) t,oddOrbitSecondForm (K := K) t} :
        Set (⋀[K]^2 (OddOrbitMode t → K))) := by
  rw [oddOrbitFirstForm_eq_path, oddOrbitSecondForm_eq_path]
  exact quadraticSpan_swap_neg _ _

def oddOrbitQuotientDegreeEquiv (t s : ℕ) :
    ExteriorQuotientDegree
      (oddPathFirstQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t))
      (oddPathSecondQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t)) s ≃ₗ[K]
    ExteriorQuotientDegree (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm (K := K) t) s :=
  exteriorQuotientDegreeGeneratorsEquiv _ _ _ _ (oddOrbit_quadraticSpan t) s

section CharacteristicZero

variable [CharZero K]

/-- The full good-word basis for the actual block orbit normal form. -/
def oddOrbitQuotientDegreeBasis (t s : ℕ) :
    Module.Basis (GoodOddIndex (t+1) s) K
      (ExteriorQuotientDegree (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm (K := K) t) s) :=
  (oddExteriorBasisAt (oddOrbitInterleavedBasis (K := K) t) s).map (oddOrbitQuotientDegreeEquiv t s)

theorem oddOrbitQuotientDegreeBasis_apply (t s : ℕ) (I : GoodOddIndex (t+1) s) :
    oddOrbitQuotientDegreeBasis (K := K) t s I = Submodule.Quotient.mk
      (exteriorPower.ιMulti K s (fun i => oddOrbitInterleavedBasis (K := K) t (I.val.val i))) := by
  rw [oddOrbitQuotientDegreeBasis, Module.Basis.map_apply, oddExteriorBasisAt_apply]
  simpa only [oddOrbitQuotientDegreeEquiv] using
    exteriorQuotientDegreeGeneratorsEquiv_mk
      (oddPathFirstQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t))
      (oddPathSecondQuadratic (K := K) (oddOrbitInterleavedBasis (K := K) t))
      (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm (K := K) t)
      (oddOrbit_quadraticSpan (K := K) t) s
      (exteriorPower.ιMulti K s (fun i => oddOrbitInterleavedBasis (K := K) t (I.val.val i)))

theorem oddOrbitQuotientDegree_finrank (t s : ℕ) :
    Module.finrank K
      (ExteriorQuotientDegree (oddOrbitFirstForm (K := K) t) (oddOrbitSecondForm (K := K) t) s) =
      Fintype.card (GoodOddIndex (t+1) s) :=
  Module.finrank_eq_card_basis (oddOrbitQuotientDegreeBasis t s)

end CharacteristicZero

end PaperVerification.AlternatingForms
