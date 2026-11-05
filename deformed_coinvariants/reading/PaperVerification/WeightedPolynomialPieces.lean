module

public import PaperVerification.PolynomialHomogeneousDerivations
public import TauCeti.RingTheory.MvPolynomial.RestrictSupport

/-!
# Finite, exactly shifted weighted polynomial pieces

The index equation is `weight(a)+shift=total`. Positive variable weights
make every index type finite. The projection is an integer-degree component,
so negative shifted degrees are literally zero rather than degree zero.
The basis and projection describe the actual polynomial submodule.

This supporting source has not yet been compiled.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.WeightedPolynomialPieces

open MvPolynomial Module PolynomialHomogeneousDerivations

variable {ι K : Type*} [CommRing K]
local notation "P" => MvPolynomial ι K

def integerWeights (w : ι → ℕ) : ι → ℤ := fun i => (w i : ℤ)

theorem integer_weight (w : ι → ℕ) (a : ι →₀ ℕ) :
    Finsupp.weight (integerWeights w) a = (Finsupp.weight w a : ℤ) := by
  simp only [integerWeights,Finsupp.weight_apply,Finsupp.sum,nsmul_eq_mul,
    Nat.cast_sum,Nat.cast_mul]

theorem homogeneous_cast_iff (w : ι → ℕ) (p : P) (j : ℕ) :
    IsWeightedHomogeneous (integerWeights w) p (j : ℤ) ↔
      IsWeightedHomogeneous w p j := by
  simp only [IsWeightedHomogeneous,integer_weight,Nat.cast_inj]

def Index (w : ι → ℕ) (s d : ℕ) := {a : ι →₀ ℕ // Finsupp.weight w a+s=d}

instance index_finite [Finite ι] (w : ι → ℕ) [∀ i, NeZero (w i)] (s d : ℕ) :
    Finite (Index w s d) := by
  have hset : Set.Finite {a : ι →₀ ℕ | Finsupp.weight w a+s=d} :=
    (Finsupp.finite_of_nat_weight_le w (fun i => NeZero.ne (w i)) d).subset (by
      intro a ha
      change Finsupp.weight w a ≤ d
      change Finsupp.weight w a+s=d at ha
      omega)
  exact hset.to_subtype

noncomputable instance index_fintype [Finite ι] (w : ι → ℕ)
    [∀ i, NeZero (w i)] (s d : ℕ) : Fintype (Index w s d) := Fintype.ofFinite _

def piece (w : ι → ℕ) (s d : ℕ) : Submodule K P :=
  restrictSupport K {a | Finsupp.weight w a+s=d}

def basis (w : ι → ℕ) (s d : ℕ) : Basis (Index w s d) K (piece (K := K) w s d) :=
  basisRestrictSupport K {a : ι →₀ ℕ | Finsupp.weight w a+s=d}

instance piece_finite [Finite ι] (w : ι → ℕ) [∀ i, NeZero (w i)] (s d : ℕ) :
    Module.Finite K (piece (K := K) w s d) := Module.Finite.of_basis (basis w s d)

theorem mem_piece (w : ι → ℕ) (s d : ℕ) (p : P) :
    p ∈ piece w s d ↔ ∀ a, p.coeff a ≠ 0 → Finsupp.weight w a+s=d := by
  simp only [piece,mem_restrictSupport_iff,Set.subset_def,
    Finset.mem_coe,MvPolynomial.mem_support_iff,Set.mem_setOf_eq]

/-- This equivalence includes every degree below the shift. -/
theorem mem_piece_iff_integer_homogeneous (w : ι → ℕ) (s d : ℕ) (p : P) :
    p ∈ piece w s d ↔
      IsWeightedHomogeneous (integerWeights w) p ((d : ℤ)-(s : ℤ)) := by
  rw [mem_piece]
  simp only [IsWeightedHomogeneous,integer_weight]
  constructor
  · intro h a ha
    have he := h a ha
    omega
  · intro h a ha
    have he := h a ha
    omega

theorem piece_eq_bot (w : ι → ℕ) {s d : ℕ} (hds : d<s) :
    piece (K := K) w s d = ⊥ := by
  apply eq_bot_iff.mpr
  intro p hp
  change p=0
  apply MvPolynomial.ext
  intro a
  have hz : p.coeff a=0 := by
    by_contra h
    have he := (mem_piece w s d p).mp hp a h
    omega
  simpa only [coeff_zero] using hz

def project (w : ι → ℕ) (s d : ℕ) : P →ₗ[K] P :=
  weightedHomogeneousComponent (integerWeights w) ((d : ℤ)-(s : ℤ))

theorem project_mem (w : ι → ℕ) (s d : ℕ) (p : P) :
    project w s d p ∈ piece w s d := by
  apply (mem_piece_iff_integer_homogeneous w s d _).mpr
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem project_of_mem (w : ι → ℕ) (s d : ℕ) {p : P}
    (hp : p ∈ piece w s d) : project w s d p=p :=
  ((mem_piece_iff_integer_homogeneous w s d p).mp hp).weightedHomogeneousComponent_same

section FiniteVariables

variable [Fintype ι]

theorem project_multiply (w : ι → ℕ) {q : P} {j : ℕ}
    (hq : IsWeightedHomogeneous w q j) (s d : ℕ) (p : P) :
    project w s d (q*p)=q*project w (s+j) d p := by
  have hqi := (homogeneous_cast_iff w q j).mpr hq
  have h := component_multiply hqi ((d : ℤ)-((s+j : ℕ) : ℤ)) p
  have he : (d : ℤ)-(s : ℤ)=((d : ℤ)-((s+j : ℕ) : ℤ))+(j : ℤ) := by omega
  simpa only [project,he] using h

theorem project_derivation (w : ι → ℕ)
    {D : Derivation K P P} {j : ℕ}
    (hD : HasDegree (integerWeights w) D (j : ℤ)) (s d : ℕ) (p : P) :
    project w s d (D p)=D (project w (s+j) d p) := by
  have h := component_derivation hD ((d : ℤ)-((s+j : ℕ) : ℤ)) p
  have he : (d : ℤ)-(s : ℤ)=((d : ℤ)-((s+j : ℕ) : ℤ))+(j : ℤ) := by omega
  simpa only [project,he] using h

end FiniteVariables
end PaperVerification.WeightedPolynomialPieces
