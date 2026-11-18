module

public import Papers.GraphicalZonotopes.BooleanLinkRows
public import Papers.GraphicalZonotopes.RefinedTriangleComponents

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.BooleanFourPartStructure
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {y : SetFunction V}

theorem clique_card_le_four (hG : G.CliqueFree 5) (D : Finset V)
    (hD : G.IsClique D) : D.card≤4 := by
  by_contra hn
  obtain ⟨E,hED,hE⟩ := exists_subset_card_eq (show 5≤D.card by omega)
  exact hG E ⟨fun u hu v hv huv => hD (hED hu) (hED hv) huv,hE⟩

theorem edge_boolean
    (hb : ∀ u v,u≠v → ∀ S,u∉S → v∉S →
      delta (zeta y) u v S=0 ∨ delta (zeta y) u v S=1)
    {u v : V} (huv : u≠v) (S : Finset V) :
    BooleanLinkRows.IsBit (zeta (edgeCoefficients y u v) S) := by
  rw [zeta_erase_of_containing_zero _ u (by intro C hC;simp [edgeCoefficients,hC])]
  rw [zeta_erase_of_containing_zero _ v (by intro C hC;simp [edgeCoefficients,hC])]
  rw [edgeCoefficients_zeta huv (by simp) (by simp)]
  exact hb u v huv _ (by simp) (by simp)

theorem edge_zero_of_nonadj (hy : CliqueSupported G y) (u v : V)
    {a b : V} (hab : a≠b) (hn : ¬G.Adj a b) :
    edgeCoefficients y u v {a,b}=0 := by
  unfold edgeCoefficients
  split_ifs
  · exact hy.2.2 _ a b (by simp) (by simp) hab hn
  · rfl

/-- Two different extensions of a triangle in a K5-free graph are nonadjacent. -/
theorem nonadjacent_above_triangle (hG : G.CliqueFree 5)
    {T : Finset V} (hT : T.card=3) {a b : V}
    (ha : a∉T) (hb : b∉T) (hab : a≠b)
    (hA : G.IsClique (insert a T : Finset V))
    (hB : G.IsClique (insert b T : Finset V)) : ¬G.Adj a b := by
  intro hadj
  have hcl : G.IsClique (insert a (insert b T) : Finset V) := by
    rw [coe_insert]
    change G.IsClique (insert a ((insert b T : Finset V) : Set V))
    apply hB.insert
    intro v hv hav
    rcases mem_insert.mp hv with rfl | hvT
    · exact hadj
    · exact hA (by simp) (by simp [hvT]) hav
  have hc := clique_card_le_four hG _ hcl
  rw [card_insert_of_notMem (by simp [hab,ha]),card_insert_of_notMem hb,hT] at hc
  omega

theorem nonadjacent_replacement (hG : G.CliqueFree 5)
    {D : Finset V} (hD : D.card=4) (hcl : G.IsClique D)
    {u x : V} (hu : u∈D) (hx : x∉D)
    (hcx : G.IsClique (insert x (D.erase u) : Finset V)) : ¬G.Adj u x := by
  apply nonadjacent_above_triangle hG (T := D.erase u)
    (by rw [card_erase_of_mem hu,hD]) (by simp)
    (fun h => hx (mem_of_mem_erase h)) (fun he => hx (he ▸ hu))
  · simpa only [insert_erase hu] using hcl
  · exact hcx

/-- Three nonzero tetrahedra cannot share one triangle. This is the literal
thinness obstruction and uses Boolean rows on all contexts. -/
theorem three_extensions_impossible (hG : G.CliqueFree 5) (hy : CliqueSupported G y)
    (hb : ∀ u v,u≠v → ∀ S,u∉S → v∉S →
      delta (zeta y) u v S=0 ∨ delta (zeta y) u v S=1)
    {T : Finset V} (hT : T.card=3) {x y' z : V}
    (hx : x∉T) (hy' : y'∉T) (hz : z∉T)
    (hxy : x≠y') (hxz : x≠z) (hyz : y'≠z)
    (hX : y (insert x T)≠0) (hY : y (insert y' T)≠0)
    (hZ : y (insert z T)≠0) : False := by
  have hclX := hy.clique_of_nonzero hX
  have hclY := hy.clique_of_nonzero hY
  have hclZ := hy.clique_of_nonzero hZ
  have hnXY := nonadjacent_above_triangle hG hT hx hy' hxy hclX hclY
  have hnXZ := nonadjacent_above_triangle hG hT hx hz hxz hclX hclZ
  have hnYZ := nonadjacent_above_triangle hG hT hy' hz hyz hclY hclZ
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := card_eq_three.mp hT
  have hax : a≠x := by intro h;exact hx (by simp [← h])
  have hay : a≠y' := by intro h;exact hy' (by simp [← h])
  have haz : a≠z := by intro h;exact hz (by simp [← h])
  have hbx : b≠x := by intro h;exact hx (by simp [← h])
  have hby : b≠y' := by intro h;exact hy' (by simp [← h])
  have hbz : b≠z := by intro h;exact hz (by simp [← h])
  have hcx : c≠x := by intro h;exact hx (by simp [← h])
  have hcy : c≠y' := by intro h;exact hy' (by simp [← h])
  have hcz : c≠z := by intro h;exact hz (by simp [← h])
  have hbad := BooleanLinkRows.no_three_leaf_star (edgeCoefficients y a b)
    (edgeCoefficients_degree_two hy (clique_card_le_four hG) hab)
    (edge_boolean hb hab) hcx hcy hcz hxy hxz hyz
    (edge_zero_of_nonadj hy a b hxy hnXY)
    (edge_zero_of_nonadj hy a b hxz hnXZ)
    (edge_zero_of_nonadj hy a b hyz hnYZ)
  have heX : insert a (insert b ({c,x} : Finset V))=insert x {a,b,c} := by
    ext v;simp [or_comm,or_left_comm,or_assoc]
  have heY : insert a (insert b ({c,y'} : Finset V))=insert y' {a,b,c} := by
    ext v;simp [or_comm,or_left_comm,or_assoc]
  have heZ : insert a (insert b ({c,z} : Finset V))=insert z {a,b,c} := by
    ext v;simp [or_comm,or_left_comm,or_assoc]
  simp only [edgeCoefficients,mem_insert,mem_singleton,hac,hax,hay,haz,hbc,hbx,hby,hbz,
    false_or,not_false_eq_true,and_self,if_true,heX,heY,heZ] at hbad
  exact hbad.elim hX (fun h => h.elim hY hZ)

/-- Two replacements in different positions complete to a fourth nonzero
tetrahedron. The two replacement vertices must be distinct. -/
theorem replacement_square (hG : G.CliqueFree 5) (hy : CliqueSupported G y)
    (hb : ∀ u v,u≠v → ∀ S,u∉S → v∉S →
      delta (zeta y) u v S=0 ∨ delta (zeta y) u v S=1)
    {D : Finset V} (hD : D.card=4) (hbase : y D≠0)
    {u v x y' : V} (hu : u∈D) (hv : v∈D) (huv : u≠v)
    (hx : x∉D) (hy' : y'∉D)
    (hX : y (insert x (D.erase u))≠0) (hY : y (insert y' (D.erase v))≠0) :
    x≠y' ∧ y (insert y' (insert x ((D.erase u).erase v)))≠0 := by
  have hcl := hy.clique_of_nonzero hbase
  have hclX := hy.clique_of_nonzero hX
  have hclY := hy.clique_of_nonzero hY
  have hnUX := nonadjacent_replacement hG hD hcl hu hx hclX
  have hnVY := nonadjacent_replacement hG hD hcl hv hy' hclY
  have hux : u≠x := fun he => hx (he ▸ hu)
  have hvx : v≠x := fun he => hx (he ▸ hv)
  have huy : u≠y' := fun he => hy' (he ▸ hu)
  have hvy : v≠y' := fun he => hy' (he ▸ hv)
  have hxy : x≠y' := by
    intro he
    apply hnUX
    rw [he]
    exact hclY (mem_insert_of_mem (mem_erase.mpr ⟨huv,hu⟩)) (mem_insert_self _ _) huy
  have hEcard : ((D.erase u).erase v).card=2 := by
    rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm huv,hv⟩),card_erase_of_mem hu,hD]
  obtain ⟨p,q,hpq,hE⟩ := card_eq_two.mp hEcard
  have hpE : p∈(D.erase u).erase v := by rw [hE];simp
  have hqE : q∈(D.erase u).erase v := by rw [hE];simp
  have hpD : p∈D := mem_of_mem_erase (mem_of_mem_erase hpE)
  have hqD : q∈D := mem_of_mem_erase (mem_of_mem_erase hqE)
  have hpu : p≠u := ne_of_mem_erase (mem_of_mem_erase hpE)
  have hpv : p≠v := ne_of_mem_erase hpE
  have hqu : q≠u := ne_of_mem_erase (mem_of_mem_erase hqE)
  have hqv : q≠v := ne_of_mem_erase hqE
  have hpx : p≠x := fun he => hx (he ▸ hpD)
  have hqx : q≠x := fun he => hx (he ▸ hqD)
  have hpy : p≠y' := fun he => hy' (he ▸ hpD)
  have hqy : q≠y' := fun he => hy' (he ▸ hqD)
  have hDrepr : insert u (insert v ({p,q} : Finset V))=D := by
    rw [← hE,insert_erase (mem_erase.mpr ⟨Ne.symm huv,hv⟩),insert_erase hu]
  have hDu : D.erase u=insert v {p,q} := by
    rw [← hDrepr];simp [huv,Ne.symm hpu,Ne.symm hqu]
  have hDv : D.erase v=insert u {p,q} := by
    ext w
    rw [← hDrepr]
    simp only [mem_erase,mem_insert,mem_singleton]
    constructor
    · rintro ⟨hwv,rfl | rfl | hw⟩
      · exact Or.inl rfl
      · exact False.elim (hwv rfl)
      · exact Or.inr hw
    · rintro (rfl | rfl | rfl)
      · exact ⟨huv,Or.inl rfl⟩
      · exact ⟨hpv,Or.inr (Or.inr (Or.inl rfl))⟩
      · exact ⟨hqv,Or.inr (Or.inr (Or.inr rfl))⟩
  have heX : insert p (insert q ({x,v} : Finset V))=insert x (D.erase u) := by
    rw [hDu];ext w;simp [or_comm,or_left_comm,or_assoc]
  have heY : insert p (insert q ({u,y'} : Finset V))=insert y' (D.erase v) := by
    rw [hDv];ext w;simp [or_comm,or_left_comm,or_assoc]
  have hnonX : edgeCoefficients y p q {x,v}≠0 := by
    simpa only [edgeCoefficients,mem_insert,mem_singleton,hpx,hpv,hqx,hqv,
      false_or,not_false_eq_true,and_self,if_true,heX] using hX
  have hnonY : edgeCoefficients y p q {u,y'}≠0 := by
    simpa only [edgeCoefficients,mem_insert,mem_singleton,hpu,hpy,hqu,hqy,
      false_or,not_false_eq_true,and_self,if_true,heY] using hY
  have hnonXY : edgeCoefficients y p q {x,y'}≠0 := by
    intro hzero
    have hm := BooleanLinkRows.no_induced_path (edgeCoefficients y p q)
      (edgeCoefficients_degree_two hy (clique_card_le_four hG) hpq)
      (edge_boolean hb hpq) (Ne.symm hvx) (Ne.symm hux) hxy (Ne.symm huv) hvy huy
      (edge_zero_of_nonadj hy p q (Ne.symm hux) (fun h => hnUX (G.adj_symm h)))
      hzero (edge_zero_of_nonadj hy p q hvy hnVY)
    exact (mul_ne_zero hnonX hnonY) hm
  refine ⟨hxy,?_⟩
  have heNew : insert p (insert q ({x,y'} : Finset V))=
      insert y' (insert x ((D.erase u).erase v)) := by
    rw [hE];ext w;simp [or_comm,or_left_comm,or_assoc]
  simpa only [edgeCoefficients,mem_insert,mem_singleton,hpx,hpy,hqx,hqy,
    false_or,not_false_eq_true,and_self,if_true,heNew] using hnonXY

end GraphicalZonotopes.BooleanFourPartStructure
