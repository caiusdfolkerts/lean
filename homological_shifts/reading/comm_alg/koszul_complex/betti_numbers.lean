import CommAlg.KoszulComplex.TorGrading
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Genuine finite multigraded Betti numbers

Over a field, every homogeneous component of the derived Tor module is finite-dimensional.
Its dimension therefore has positive support exactly at the degree components used to define
homological shift ideals.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 2500
namespace CommAlg.Koszul
open Classical CommAlg.Polymatroid CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

instance homogeneousPiece_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    FiniteDimensional k (homogeneousPiece (k := k) B a i) := by
  letI : FiniteDimensional k (Simplicial.Chains (k := k) (koszulFaces B a) i) :=
    (faceChainBasis (k := k) B a i).finiteDimensional_of_finite
  exact FiniteDimensional.of_injective (faceHomogeneousEquiv (k := k) B a i).symm.toLinearMap
    (faceHomogeneousEquiv (k := k) B a i).symm.injective

instance homogeneousHomology_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    FiniteDimensional k ((homogeneousComplex (k := k) B a).homology i) := by
  let K := homogeneousComplex (k := k) B a
  letI : FiniteDimensional k (K.X i) := homogeneousPiece_finite B a i
  letI : FiniteDimensional k (K.cycles i) :=
    FiniteDimensional.of_injective (K.iCycles i).hom
      ((ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance)
  exact FiniteDimensional.of_surjective (K.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance)

instance gradedTor_finite (B : Family V) (a : Exponent V) (i : ℕ) :
    FiniteDimensional k (gradedTor (k := k) B a i) := by
  exact FiniteDimensional.of_injective (gradedTorIso (k := k) B a i).inv.hom
    ((ModuleCat.mono_iff_injective (gradedTorIso (k := k) B a i).inv).mp inferInstance)

/-- The actual multigraded Betti number: dimension of the corresponding derived Tor component. -/
def bettiNumber (B : Family V) (a : Exponent V) (i : ℕ) : ℕ :=
  Module.finrank k (gradedTor (k := k) B a i)

lemma bettiNumber_pos_iff (B : Family V) (a : Exponent V) (i : ℕ) :
    0 < bettiNumber (k := k) B a i ↔ GradedBettiNonzero (k := k) B a i := by
  unfold bettiNumber GradedBettiNonzero
  rw [Nat.pos_iff_ne_zero]
  have he : Module.finrank k (gradedTor (k := k) B a i) = 0 ↔
      Subsingleton (gradedTor (k := k) B a i) :=
    Module.finrank_zero_iff (R := k) (M := gradedTor (k := k) B a i)
  exact (not_congr he).trans (not_congr (ModuleCat.isZero_iff_subsingleton
    (M := ModuleCat.of k (gradedTor (k := k) B a i))).symm)

lemma bettiNumber_pos_iff_faces (B : Family V) (a : Exponent V) (i : ℕ) :
    0 < bettiNumber (k := k) B a i ↔
      Simplicial.NonzeroHomology (k := k) (koszulFaces B a) i := by
  rw [bettiNumber_pos_iff, gradedBettiNonzero_iff_faces]

end CommAlg.Koszul
