import Characterizations.Isolators.Mixed
import Characterizations.Transport
import Characterizations.Strands.BettiTransport
import CommAlg.Polymatroid.IdealProducts

/-! # Common monomial factors: actual ideals, localization, and derived Betti numbers -/
noncomputable section
set_option maxHeartbeats 600000
namespace Characterizations.Isolators
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

lemma translatedFamily_antichain {B : Family V} (hB : Antichain B) (c : Exponent V) :
    Antichain (translatedFamily c B) := by
  rintro a ha b hb hab
  obtain ⟨a, ha₀, rfl⟩ := (Finset.mem_image (s := B) (f := fun a => a+c)).mp ha
  obtain ⟨b, hb₀, rfl⟩ := (Finset.mem_image (s := B) (f := fun b => b+c)).mp hb
  exact congrArg (· + c) (hB a ha₀ b hb₀ (add_le_add_iff_right c |>.mp hab))

lemma translatedFamily_nonempty {B : Family V} (hB : B.Nonempty) (c : Exponent V) :
    (translatedFamily c B).Nonempty := hB.image _

lemma localFamily_translated (B : Family V) (c : Exponent V) (R : Finset V) :
    localFamily (translatedFamily c B) R =
      translatedFamily (restrictExponent R c) (localFamily B R) := by
  let f : Exponent R ↪o Exponent R := OrderEmbedding.ofMapLEIff
    (fun b => b + restrictExponent R c) (fun _ _ => add_le_add_iff_right _)
  have hh := minimalFamily_image_orderEmbedding f (B.image (restrictExponent R))
  have hadd : ∀ b, restrictExponent R (b+c) = restrictExponent R b + restrictExponent R c := by
    intro b; ext i; rfl
  simpa only [localFamily, translatedFamily, Finset.image_image, Function.comp_def,
    hadd, f, OrderEmbedding.coe_ofMapLEIff] using hh

lemma monomialIdeal_translated (k : Type*) [CommSemiring k] (B : Family V) (c : Exponent V) :
    monomialIdeal k (translatedFamily c B) =
      monomialIdeal k B * Ideal.span {MvPolynomial.monomial c (1 : k)} := by
  have hs : monomialIdeal k ({c} : Family V) = Ideal.span {MvPolynomial.monomial c (1 : k)} := by
    unfold monomialIdeal
    congr 1
    ext p
    simp
  rw [← hs, monomialIdeal_mul]
  congr 1
  ext a
  simp [translatedFamily]

lemma translatedFamily_locallyEquigenerated {B : Family V}
    (hB : LocallyEquigenerated B) (c : Exponent V) :
    LocallyEquigenerated (translatedFamily c B) := by
  apply (locallyEquigenerated_iff _).mpr
  intro R
  obtain ⟨d, hd⟩ := (locallyEquigenerated_iff _).mp hB R
  rw [localFamily_translated]
  exact ⟨_, translatedFamily_equigenerated hd _⟩

lemma translated_deletedBounded_linearResolution {k : Type u} [CommRing k] [Nontrivial k]
    (d : ℕ) (T : Finset V) (h c : Exponent V)
    (hsat : ∀ i ∈ T, h i = 1) (hT : T.Nonempty) :
    Nonempty (LinearResolution
      (monomialIdeal k (translatedFamily c (deletedBounded d T h))) (d+c.degree)) := by
  obtain ⟨w, hw⟩ := hT
  obtain ⟨o, ho⟩ := exists_lastVariable w
  apply linearResolution_of_linearQuotients _ _
    (translatedFamily_equigenerated (deletedBounded_equigenerated d T h) c)
    (variableRevlex o) (variableRevlex_irrefl o) (fun hab hbc => variableRevlex_trans o hab hbc)
    (variableRevlex_total o)
  exact (translatedFamily_linearQuotients_iff (deletedBounded_equigenerated d T h) c o).mpr
    (deletedBounded_linearQuotients_last d T h hsat o w hw ho)

section Betti
variable [LinearOrder V]
variable {k : Type u} [Field k]

lemma koszulFaces_translated (B : Family V) (a c : Exponent V) :
    koszulFaces (translatedFamily c B) (a+c) = koszulFaces B a := by
  funext s
  apply propext
  constructor
  · rintro ⟨hf, b, hb, hba⟩
    obtain ⟨b, hb₀, rfl⟩ := (Finset.mem_image (s := B) (f := fun b => b+c)).mp hb
    have hf' : faceExponent s ≤ a := by
      intro i
      have h1 := hf i
      have h2 := hba i
      simp only [Finsupp.add_apply, Finsupp.tsub_apply] at h1 h2
      omega
    refine ⟨hf', b, hb₀, ?_⟩
    intro i
    have h1 := hf' i
    have h2 := hba i
    simp only [Finsupp.add_apply, Finsupp.tsub_apply] at h2 ⊢
    omega
  · rintro ⟨hf, b, hb, hba⟩
    refine ⟨hf.trans (by intro j; exact Nat.le_add_right _ _), b+c, mem_image.mpr ⟨b, hb, rfl⟩, ?_⟩
    intro i
    have h1 := hf i
    have h2 := hba i
    simp only [Finsupp.add_apply, Finsupp.tsub_apply] at h2 ⊢
    omega

lemma koszulFaces_translated_outside (B : Family V) (a c : Exponent V) (hc : ¬ c ≤ a) :
    koszulFaces (translatedFamily c B) a = fun _ => False := by
  funext s
  apply propext
  constructor
  · rintro ⟨hf, b, hb, hba⟩
    obtain ⟨b, hb₀, rfl⟩ := (Finset.mem_image (s := B) (f := fun b => b+c)).mp hb
    apply hc
    intro i
    have hh := hba i
    simp only [Finsupp.add_apply, Finsupp.tsub_apply] at hh
    omega
  · exact False.elim

lemma gradedBetti_translated (B : Family V) (a c : Exponent V) (i : ℕ) :
    GradedBettiNonzero (k := k) (translatedFamily c B) (a+c) i ↔
      GradedBettiNonzero (k := k) B a i := by
  rw [gradedBettiNonzero_iff_faces, gradedBettiNonzero_iff_faces, koszulFaces_translated]

lemma bettiNumber_translated (B : Family V) (a c : Exponent V) (i : ℕ) :
    bettiNumber (k := k) (translatedFamily c B) (a+c) i = bettiNumber (k := k) B a i := by
  rw [Strands.bettiNumber_eq_face_homology_finrank, Strands.bettiNumber_eq_face_homology_finrank]
  rw [Strands.chainComplex_congr _ _ (koszulFaces_translated B a c)]

lemma bettiNumber_translated_outside (B : Family V) (a c : Exponent V) (i : ℕ)
    (hc : ¬ c ≤ a) : bettiNumber (k := k) (translatedFamily c B) a i = 0 := by
  apply Strands.bettiNumber_eq_zero_of_exact
  apply exactIn_of_no_face
  intro s hs
  rw [koszulFaces_translated_outside B a c hc] at hs
  exact hs.elim

end Betti
end Characterizations.Isolators
