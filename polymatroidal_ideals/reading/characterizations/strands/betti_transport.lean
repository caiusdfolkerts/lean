import Characterizations.Strands.SimplexHomology
import CommAlg.KoszulComplex.BettiNumbers

/-! # Numerical transport to the genuine derived-Tor components -/
noncomputable section
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial
open CategoryTheory CategoryTheory.Limits
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

lemma chainComplex_congr {K L : Finset V → Prop} (hK : Downward K) (hL : Downward L)
    (h : K = L) : chainComplex (k := k) hK = chainComplex hL := by
  subst L
  rfl

lemma bettiNumber_eq_face_homology_finrank (B : Family V) (a : Exponent V) (i : ℕ) :
    bettiNumber (k := k) B a i =
      Module.finrank k ((chainComplex (k := k) (koszulFaces_downward B a)).homology i) := by
  let e := (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) i).mapIso
    (homogeneousFacesIso (k := k) B a)
  exact (e ≪≫ gradedTorIso (k := k) B a i).toLinearEquiv.finrank_eq.symm

lemma bettiNumber_eq_one_of_boundary (B : Family V) (a : Exponent V)
    (T : Finset V) (i : ℕ) (hcard : T.card = i+1)
    (hfaces : koszulFaces B a = simplexBoundary T) :
    bettiNumber (k := k) B a i = 1 := by
  rw [bettiNumber_eq_face_homology_finrank]
  rw [chainComplex_congr (koszulFaces_downward B a) (simplexBoundary_downward T) hfaces]
  exact simplexBoundary_homology_finrank T i hcard

lemma bettiNumber_eq_zero_of_exact (B : Family V) (a : Exponent V) (i : ℕ)
    (h : ExactIn (k := k) (koszulFaces B a) i) : bettiNumber (k := k) B a i = 0 := by
  apply Nat.eq_zero_of_not_pos
  rw [bettiNumber_pos_iff_faces, nonzeroHomology_iff_not_exactIn]
  exact not_not.mpr h

lemma bettiNumber_congr_faces (B C : Family V) (a b : Exponent V) (i : ℕ)
    (h : koszulFaces B a = koszulFaces C b) :
    bettiNumber (k := k) B a i = bettiNumber (k := k) C b i := by
  rw [bettiNumber_eq_face_homology_finrank, bettiNumber_eq_face_homology_finrank,
    chainComplex_congr (koszulFaces_downward B a) (koszulFaces_downward C b) h]

lemma bettiNumber_congr_contains (B C : Family V) (a : Exponent V) (i : ℕ)
    (h : ∀ b, Contains B b ↔ Contains C b) :
    bettiNumber (k := k) B a i = bettiNumber (k := k) C a i := by
  apply bettiNumber_congr_faces
  funext s
  exact propext (and_congr_right (fun _ => h _))

end Characterizations.Strands
