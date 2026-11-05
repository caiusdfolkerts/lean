module

public import Papers.GraphicalZonotopes.FourColorResource
public import Papers.GraphicalZonotopes.AdmissibleAttachment

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace GraphicalZonotopes.FourPartSpanning
open Finset Function FourColorResource FourPartThreeTreeCounts
variable {V : Type*} [Fintype V] [DecidableEq V]

def colorSize (c : V → Fin 4) (i : Fin 4) : ℕ :=
  ((univ : Finset V).filter (fun v => c v=i)).card

/-- Realize a complete color schedule inside any fixed finite ambient vertex
set with enough vertices in each color. All unused vertices remain isolated. -/
theorem realize_schedule (c : V → Fin 4) {a : Fin 4 → ℕ} (hs : Schedule a) :
    (∀ i,a i≤colorSize c i) →
      ∃ S : Finset V,∃ G : SimpleGraph V,ThreeTreeOn S G ∧ Admissible G ∧ Proper c G ∧
        ∀ i,(S.filter (fun v => c v=i)).card=a i := by
  induction hs with
  | initial =>
    intro hbound
    have hw : ∀ i : Fin 4,∃ v : V,c v=i := by
      intro i
      obtain ⟨v,hv⟩ := card_pos.mp (show 0<((univ : Finset V).filter (fun v => c v=i)).card from
        lt_of_lt_of_le Nat.zero_lt_one (hbound i))
      exact ⟨v,(mem_filter.mp hv).2⟩
    choose w hw using hw
    let S := (univ : Finset (Fin 4)).image w
    have hwinj : Injective w := by
      intro i j he
      have h := congrArg c he
      rwa [hw i,hw j] at h
    have hS : S.card=4 := by simp [S,card_image_of_injective _ hwinj]
    have hc : Proper c (cliqueGraph S) := by
      intro u v h he
      obtain ⟨i,_,hi⟩ := mem_image.mp h.2.1
      obtain ⟨j,_,hj⟩ := mem_image.mp h.2.2
      have hij : i=j := by rw [← hw i,← hw j,hi,hj];exact he
      exact h.1 (hi.symm.trans ((congrArg w hij).trans hj))
    have hcl : (cliqueGraph S).IsClique S := fun u hu v hv huv => ⟨huv,hu,hv⟩
    refine ⟨S,cliqueGraph S,ThreeTreeOn.tetrahedron S hS,?_,hc,?_⟩
    · intro T hT ht
      unfold triangleMultiplicity
      calc
        ((tetrahedra (cliqueGraph S)).filter (fun C => T⊆C)).card≤
            (tetrahedra (cliqueGraph S)).card := card_filter_le _ _
        _=1 := by rw [tetrahedra_cliqueGraph hS,card_singleton]
        _≤3 := by omega
    · exact fun i => color_count_tetrahedron hc hS hcl i
  | @add a hs i hcapacity ih =>
    intro hbound
    have holdbound : ∀ j,a j≤colorSize c j := by
      intro j
      have h := hbound j
      by_cases hji : j=i
      · subst j;simp only [update_self] at h;omega
      · simpa only [update_of_ne hji] using h
    obtain ⟨S,G,h3,hA,hc,hcounts⟩ := ih holdbound
    have hsize : S.card=total a := by
      rw [← sum_color_counts S c]
      exact sum_congr rfl (fun j _ => hcounts j)
    have hpos : (0 : ℤ)<2*(S.card : ℤ)-3*((S.filter (fun v => c v=i)).card : ℤ)-3 := by
      rw [hcounts i,hsize]
      omega
    obtain ⟨T,hT,hcl,havoid,hfree⟩ := free_triangle h3 hc i hpos
    have hTS : T⊆S := h3.clique_subset_active (by omega) hcl
    have hex : ∃ u : V,c u=i ∧ u∉S := by
      by_contra hn
      have hsub : (univ : Finset V).filter (fun v => c v=i)⊆S.filter (fun v => c v=i) := by
        intro u hu
        have hcu := (mem_filter.mp hu).2
        have huS : u∈S := by
          by_contra hnot
          exact hn ⟨u,hcu,hnot⟩
        exact mem_filter.mpr ⟨huS,hcu⟩
      have hcard := card_le_card hsub
      rw [hcounts i] at hcard
      have hi := hbound i
      simp only [update_self] at hi
      change a i+1≤((univ : Finset V).filter (fun v => c v=i)).card at hi
      omega
    obtain ⟨u,hcu,hu⟩ := hex
    refine ⟨insert u S,G⊔attachmentStar u T,h3.attach u hu T hT hTS hcl,
      h3.admissible_attach hA hu hT hTS hcl hfree,?_,?_⟩
    · apply proper_attachment hc
      simpa only [hcu] using havoid
    · intro j
      rw [color_count_insert S c hu j,hcounts j,hcu]
      by_cases hji : j=i
      · subst j;simp
      · simp [update_of_ne hji,Ne.symm hji]

/-- The exact arithmetic balance condition gives an actual admissible
spanning 3-tree inside the graph of different colors. -/
theorem spanning_of_balanced_colors (c : V → Fin 4)
    (ha : Balanced (colorSize c)) :
    ∃ G : SimpleGraph V,IsThreeTree G ∧ Admissible G ∧ Proper c G := by
  obtain ⟨S,G,h3,hA,hc,hcounts⟩ := realize_schedule c (schedule_of_balanced ha) (fun _ => le_rfl)
  have hcard : S.card=(univ : Finset V).card := by
    rw [← sum_color_counts S c,← sum_color_counts (univ : Finset V) c]
    exact sum_congr rfl (fun i _ => hcounts i)
  have hS : S=univ := eq_of_subset_of_card_le (subset_univ S) hcard.ge
  rw [hS] at h3
  exact ⟨G,h3,hA,hc⟩

theorem sigma_colorSize (a : Fin 4 → ℕ) (i : Fin 4) :
    colorSize (fun v : Σ j : Fin 4,Fin (a j) => v.1) i=a i := by
  let e : {v : (Σ j : Fin 4,Fin (a j)) // v.1=i} ≃ Fin (a i) :=
    { toFun := fun v => by rcases v with ⟨⟨j,b⟩,hj⟩;change j=i at hj;subst j;exact b
      invFun := fun b => ⟨⟨i,b⟩,rfl⟩
      left_inv := by rintro ⟨⟨j,b⟩,hj⟩;change j=i at hj;subst j;rfl
      right_inv := by intro b;rfl }
  have h := Fintype.card_congr e
  simpa [colorSize,Fintype.card_subtype] using h

/-- Spanning existence, with the literal maximum part-size inequality. -/
theorem four_partite_spanning_iff (a : Fin 4 → ℕ) (ha : ∀ i,1≤a i) :
    HasAdmissibleSpanningThreeTree (fourPartite a) ↔
      3*(univ.sup a)≤2*(∑ i,a i)-3 := by
  have htotal : Fintype.card (Σ i : Fin 4,Fin (a i))=∑ i,a i := by simp
  have hN : 4≤total a := total_ge_four ha
  constructor
  · rintro ⟨G,hG,h3,hA⟩
    have hc : Proper (fun v : Σ i : Fin 4,Fin (a i) => v.1) G :=
      fun u v huv => hG huv
    have hbounds : ∀ i,3*a i+3≤2*total a := by
      intro i
      have h := capacity_nonnegative h3 hc hA i
      change (0 : ℤ)≤2*((univ : Finset (Σ i : Fin 4,Fin (a i))).card : ℤ)-
        3*(colorSize (fun v : Σ i : Fin 4,Fin (a i) => v.1) i : ℤ)-3 at h
      rw [sigma_colorSize,card_univ,htotal] at h
      dsimp [total]
      omega
    obtain ⟨i,hi,he⟩ := exists_mem_eq_sup (univ : Finset (Fin 4)) (by simp) a
    have hb := hbounds i
    rw [he]
    dsimp [total] at hb
    omega
  · intro hb
    have hbal : Balanced a := by
      refine ⟨ha,?_⟩
      intro i
      have hi : a i≤univ.sup a := le_sup (mem_univ _)
      dsimp [total] at *
      omega
    have hcolors : Balanced (colorSize (fun v : Σ i : Fin 4,Fin (a i) => v.1)) := by
      have he : colorSize (fun v : Σ i : Fin 4,Fin (a i) => v.1)=a := funext (sigma_colorSize a)
      rwa [he]
    obtain ⟨G,h3,hA,hc⟩ := spanning_of_balanced_colors _ hcolors
    exact ⟨G,fun u v huv => hc u v huv,h3,hA⟩

end GraphicalZonotopes.FourPartSpanning
