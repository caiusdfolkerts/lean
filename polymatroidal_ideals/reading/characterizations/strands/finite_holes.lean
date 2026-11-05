import Characterizations.Strands.DeletedFaces
import Characterizations.Strands.BettiTransport
import CommAlg.Polymatroid.HomologicalMain

/-! # Exact regularity bounds from a finite collection of missing monomials -/
noncomputable section
set_option maxHeartbeats 600000
namespace Characterizations.Strands
open Classical Finset CommAlg.Polymatroid CommAlg.Koszul CommAlg.Simplicial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

lemma chains_le_of_faces_at_degree {K L : Finset V → Prop} (i : ℕ)
    (h : ∀ s, K s → s.card = i → L s) : Chains (k := k) K i ≤ Chains L i := by
  apply Submodule.span_mono
  rintro z ⟨s, ⟨hs, hc⟩, rfl⟩
  exact ⟨s, ⟨h s hs hc, hc⟩, rfl⟩

lemma polymatroidal_faces_exact_off_linear (B : Family V) (hB : B.Nonempty)
    (d : ℕ) (hdeg : Equigenerated B d) (hpoly : IsPolymatroidal B)
    (a : Exponent V) (i : ℕ) (hoff : a.degree ≠ d+i) :
    ExactIn (k := k) (koszulFaces B a) i := by
  by_contra hex
  have hn := (nonzeroHomology_iff_not_exactIn _ _).mpr hex
  let g := canonicalRank B hB d hdeg hpoly
  have hr : rankBases g = B := rankBases_canonical B hB d hdeg hpoly
  have hn' : NonzeroHomology (k := k) (koszulFaces (rankBases g) a) i := by
    simpa only [hr] using hn
  have hm := (koszulFaces_nonzeroHomology_iff_rankShiftFamily g a i).mp hn'
  have hd := ((mem_rankShiftFamily_iff g i a).mp hm).1
  have hg : g Finset.univ = d := by
    change upperRank B Finset.univ = d
    obtain ⟨b, hb, he⟩ := upperRank_attained hB Finset.univ
    simpa only [subsetSum_univ, hdeg b hb] using he.symm
  exact hoff (by simpa only [hg] using hd)

lemma exactIn_of_finite_holes (B C : Family V)
    (hincl : ∀ a, Contains B a → Contains C a) (t : ℕ)
    (hholes : ∀ a, Contains C a → ¬Contains B a → a.degree ≤ t)
    (a : Exponent V) (i : ℕ) (hlarge : t+i+1 < a.degree)
    (hC : ExactIn (k := k) (koszulFaces C a) i) :
    ExactIn (k := k) (koszulFaces B a) i := by
  intro z hz hc
  have hzC : z ∈ Chains (koszulFaces C a) i :=
    chains_mono (fun s hs => ⟨hs.1, hincl _ hs.2⟩) i hz
  obtain ⟨y, hy, he⟩ := hC z hzC hc
  refine ⟨y, ?_, he⟩
  apply chains_le_of_faces_at_degree (i+1) (K := koszulFaces C a) _ hy
  intro s hs hcard
  refine ⟨hs.1, ?_⟩
  by_contra hnot
  have hb := hholes (a-faceExponent s) hs.2 hnot
  have hd := degree_sub_faceExponent hs.1
  omega

lemma finite_holes_betti_degree_bound (B C : Family V)
    (hincl : ∀ a, Contains B a → Contains C a) (t : ℕ)
    (hholes : ∀ a, Contains C a → ¬Contains B a → a.degree ≤ t)
    (hC : C.Nonempty) (d : ℕ) (hdeg : Equigenerated C d)
    (hpoly : IsPolymatroidal C) (hd : d ≤ t+1)
    (a : Exponent V) (i : ℕ) (hbeta : bettiNumber (k := k) B a i ≠ 0) :
    a.degree ≤ t+i+1 := by
  by_contra hle
  have hl : t+i+1 < a.degree := by omega
  have hnonzero := (bettiNumber_pos_iff_faces B a i).mp (Nat.pos_of_ne_zero hbeta)
  have hnot := (nonzeroHomology_iff_not_exactIn _ _).mp hnonzero
  apply hnot (exactIn_of_finite_holes B C hincl t hholes a i hl _)
  exact polymatroidal_faces_exact_off_linear C hC d hdeg hpoly a i (by omega)

end Characterizations.Strands
