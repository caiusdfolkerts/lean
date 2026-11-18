module
public import Mathlib
public import characterizations
/-! The original substantive development supplies the complete proofs of the selected recognition, integral-closure, presentation, and sharp testing results. -/

@[expose] public noncomputable section
open scoped BigOperators
namespace PalomarPolymatroidal.Simplicial
variable {V k : Type*} [Fintype V] [LinearOrder V] [CommRing k]
/-- The actual exterior algebra of the coordinate vector space. -/
abbrev Ambient (V k : Type*) [Fintype V] [CommRing k] := ExteriorAlgebra k (V → k)
/-- Its standard exterior basis indexed by coordinate subsets. -/
def basis : Module.Basis (Finset V) k (Ambient V k) := (Pi.basisFun k V).ExteriorAlgebra
/-- Actual augmented chains on the displayed faces in exterior degree i. -/
def Chains (F : Finset V → Prop) (i : ℕ) : Submodule k (Ambient V k) :=
  Submodule.span k (basis '' {s | F s ∧ s.card = i})
/-- The signed augmented boundary is literal exterior contraction by the sum
of the coordinate functionals. -/
abbrev boundary : Ambient V k →ₗ[k] Ambient V k :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm k (V → k)))
    (Fintype.linearCombination k (fun _ : V => (1 : k)))
/-- Every actual cycle in this degree is filled by a chain in the next degree. -/
def ExactIn (F : Finset V → Prop) (i : ℕ) : Prop :=
  ∀ z : Ambient V k, z ∈ Chains F i → boundary z = 0 →
    ∃ y : Ambient V k, y ∈ Chains F (i + 1) ∧ boundary y = z
end PalomarPolymatroidal.Simplicial
namespace PalomarPolymatroidal
open Classical CommAlg.Polymatroid Characterizations
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]
/-- The squarefree exponent carried by an exterior coordinate subset. -/
def faceExponent (s : Finset V) : Exponent V := ∑ j ∈ s, Finsupp.single j 1
/-- The literal multidegree-a ideal Koszul faces: the residual monomial lies
in the displayed actual monomial ideal. -/
def koszulFaces (B : Family V) (a : Exponent V) (s : Finset V) : Prop :=
  faceExponent s ≤ a ∧ ∃ b ∈ B, b ≤ a - faceExponent s
/-- Exactness of the actual retained-variable Koszul chains through position t,
in every fine multidegree outside the linear total-degree strand. -/
def LocalKoszulLinearThrough (B : Family V) (U : Finset V) (e t : ℕ) : Prop :=
  ∀ a : Exponent U, ∀ i : ℕ, i ≤ t → a.degree ≠ e + i →
    Simplicial.ExactIn (k := k) (koszulFaces (localFamily B U) a) i
end PalomarPolymatroidal

namespace PalomarPolymatroidal
open Classical CommAlg.Polymatroid Characterizations
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

/-- The genuine retained-variable derived-Tor Betti number vanishes exactly
when the displayed actual exterior Koszul cycle condition is exact. -/
private theorem exactIn_iff_betti_zero (B : Family V) (a : Exponent V) (i : ℕ) :
    Simplicial.ExactIn (k := k) (koszulFaces B a) i ↔
      CommAlg.Koszul.bettiNumber (k := k) B a i = 0 := by
  have positive : 0 < CommAlg.Koszul.bettiNumber (k := k) B a i ↔
      ¬Simplicial.ExactIn (k := k) (koszulFaces B a) i :=
    (CommAlg.Koszul.bettiNumber_pos_iff_faces B a i).trans
      (CommAlg.Simplicial.nonzeroHomology_iff_not_exactIn _ _)
  constructor
  · intro h
    apply Nat.eq_zero_of_not_pos
    intro hp
    exact (positive.mp hp) h
  · intro hz
    by_contra h
    have hp := positive.mpr h
    omega

private theorem localTests_agree (B : Family V) (U : Finset V) (e t : ℕ) :
    LocalKoszulLinearThrough (k := k) B U e t ↔
      Characterizations.RetainedLinearThrough (k := k) B U e t := by
  unfold LocalKoszulLinearThrough Characterizations.RetainedLinearThrough
  simp only [exactIn_iff_betti_zero]

/-- The explicit bridge to the manuscript's exact argument order Tor_i(I_U,k),
including the proved tensor-braiding and total-grading comparison. -/
private theorem localTests_agree_paperTor (B : Family V) (U : Finset V) (e t : ℕ) :
    LocalKoszulLinearThrough (k := k) B U e t ↔
      Characterizations.PaperRetainedTorLinearThrough (k := k) B U e t :=
  (localTests_agree B U e t).trans
    ((Characterizations.retainedLinearThrough_iff_totalTor B U e t).trans
      (Characterizations.paperRetainedTorLinearThrough_iff B U e t).symm)

theorem degree_cutoff_iff (B : Family V) (hB : B.Nonempty) (hanti : Antichain B) :
    IsPolymatroidal B ↔ ∀ U : Finset V, ∃ e,
      Equigenerated (localFamily B U) e ∧
        (0 < e → LocalKoszulLinearThrough (k := k) B U e (e - 1)) := by
  simpa only [← localTests_agree_paperTor] using
    (Characterizations.polymatroidal_iff_degree_tests_paperTor (k := k) hB hanti)

theorem degree_dimension_cutoff_iff (B : Family V) (hB : B.Nonempty) (hanti : Antichain B) :
    IsPolymatroidal B ↔ ∀ U : Finset V, ∃ e,
      Equigenerated (localFamily B U) e ∧
        (0 < e → LocalKoszulLinearThrough (k := k) B U e (min (e - 1) (U.card - 1))) := by
  simpa only [← localTests_agree_paperTor] using
    (Characterizations.polymatroidal_iff_degree_dimension_tests_paperTor (k := k) hB hanti)

theorem triangular_cutoff_iff (B : Family V) (hB : B.Nonempty) {d : ℕ}
    (hd : Equigenerated B d) (hd2 : 2 ≤ d) : IsPolymatroidal B ↔
    ∀ U : Finset V, 2 ≤ U.card → Fintype.card V - U.card ≤ d - 1 →
      ∃ e, Equigenerated (localFamily B U) e ∧
        (0 < e → LocalKoszulLinearThrough (k := k) B U e
          (min (e - 1) (min (d - 1 - (Fintype.card V - U.card)) (U.card - 1)))) := by
  simpa only [← localTests_agree_paperTor] using
    (Characterizations.polymatroidal_iff_triangular_paperTor (k := k) hB hd hd2)
end PalomarPolymatroidal
