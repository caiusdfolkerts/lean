import Characterizations.PatternSpace
import Characterizations.SignatureBound
import Characterizations.HighDegreeNumbers

/-! # The numerical upper and lower bounds of Corollary 5.5 -/

noncomputable section
set_option maxHeartbeats 1000000
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
variable {V : Type*} [Fintype V] [DecidableEq V]

def testProbability (d : ℕ) : ℝ := 2 / ((d:ℝ)*((d:ℝ)+1)*((d:ℝ)+2))

theorem inverse_point_count_eq_probability (s : ℕ) :
    (1 / ((s+3)*(s+2).choose 2 : ℕ) : ℝ) = testProbability (s+1) := by
  have hn := Nat.add_one_mul_choose_eq (s+1) 1
  have hn' : ((s+2).choose 2 : ℝ)*2 = ((s:ℝ)+1)*((s:ℝ)+2) := by
    have hh : (s+2).choose 2*2 = (s+1)*(s+2) := by simpa [mul_comm] using hn.symm
    exact_mod_cast hh
  have hpos : (0:ℝ) < (s+2).choose 2 := by exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ s+2))
  unfold testProbability
  push_cast
  field_simp
  nlinarith

theorem exists_degree_test_family_logarithmic {k : Type*} [CommSemiring k] [Nontrivial k]
    (d : ℕ) (hd : 2 ≤ d) (hcard : 4 ≤ Fintype.card V) (hdn : d ≤ Fintype.card V-2) :
    ∃ F : Finset (VariableOrder V), DegreeOrderTests k d (F : Set (VariableOrder V)) ∧
      F.card ≤ ⌈(testProbability d)⁻¹ *
        (Real.log (Fintype.card V * (Fintype.card V-1).choose 2 *
          (Fintype.card V-3).choose (d-1)) + 1)⌉₊ := by
  letI : Nonempty (VariableOrder V) := ⟨Fintype.equivFin V⟩
  letI : Nonempty (DegreePattern V (d-1)) := degreePattern_nonempty (d-1) (by omega)
  have hp : 0 < testProbability d := by unfold testProbability; positivity
  have hR (P : DegreePattern V (d-1)) :
      finiteFraction (fun o : VariableOrder V => RealizesPattern o P) = testProbability d := by
    rw [realizesPattern_probability,inverse_point_count_eq_probability]
    congr 1
    omega
  obtain ⟨F,hsize,hcover⟩ := finite_probabilistic_cover
    (fun (P : DegreePattern V (d-1)) (o : VariableOrder V) => RealizesPattern o P)
    (testProbability d) hp hR
  have hpat : CoversPatterns (d-1) (F : Set (VariableOrder V)) :=
    (coversPatterns_iff_degreePattern _).mpr hcover
  have hmin : min (d-1) (Fintype.card V-3) = d-1 := by omega
  refine ⟨F,(degreeOrderTests_iff_coverage d hd hcard _).mpr ⟨by rw [hmin]; exact hpat,?_⟩,?_⟩
  · intro hn
    omega
  · have hcount : Fintype.card (DegreePattern V (d-1)) =
        Fintype.card V * (Fintype.card V-1).choose 2 * (Fintype.card V-3).choose (d-1) := by
      simpa only [Nat.card_eq_fintype_card] using card_degreePattern_paper (V := V) (d-1) (by omega)
    simpa only [hcount,Nat.cast_mul] using hsize

theorem degree_test_number_lower_bound {k : Type*} [CommSemiring k] [Nontrivial k]
    (d : ℕ) (hd : 2 ≤ d) (hcard : 4 ≤ Fintype.card V) (hdn : d ≤ Fintype.card V-2)
    (F : Finset (VariableOrder V)) (hF : DegreeOrderTests k d (F : Set (VariableOrder V))) :
    3 * (d+2).choose 3 ≤ F.card := by
  obtain ⟨T,hT,hTc⟩ := exists_subset_card_eq (show d+2 ≤ (univ : Finset V).card by simp; omega)
  let e : T ↪ V := Function.Embedding.subtype _
  let F' : Finset (VariableOrder T) := F.image (fun o => restrictedOrder o e)
  have hpatterns := ((degreeOrderTests_iff_coverage d hd hcard _).mp hF).1
  have hmin : min (d-1) (Fintype.card V-3) = d-1 := by omega
  rw [hmin] at hpatterns
  have hcover := (coversPatterns_iff_degreePattern _).mp hpatterns
  have htriples : CoversFinalTriples (F' : Set (VariableOrder T)) := by
    intro i q j hiq hij hqj
    have hTcard : T.card = (d-1)+3 := by omega
    let P : DegreePattern V (d-1) := ⟨⟨T,hTcard⟩,⟨j,⟨{i,q},
      by simp [insert_subset_iff,hij,hqj],by simp [hiq]⟩⟩⟩
    obtain ⟨o,ho,hp⟩ := hcover P
    refine ⟨restrictedOrder o e,mem_image.mpr ⟨o,ho,rfl⟩,?_⟩
    exact (coversPoint_pair_iff hiq hij hqj).mp hp
  have hh := triple_coverage_card_lower_bound F' htriples
  rw [Fintype.card_coe,hTc,pointedTriple_count_formula (d+2) (by omega)] at hh
  exact hh.trans (card_image_le)

end Characterizations
