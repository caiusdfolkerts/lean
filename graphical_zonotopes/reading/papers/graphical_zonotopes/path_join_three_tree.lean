module

public import Papers.GraphicalZonotopes.PathJoinCliques
public import Papers.GraphicalZonotopes.ThreeTreeCliques
public import Papers.GraphicalZonotopes.TetrahedralGrowth
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace GraphicalZonotopes.PathJoin
open Finset
open scoped Classical
attribute [local instance] Classical.propDecidable

def vertexPrefix (n k : ℕ) : Finset (Vertex n) := univ.filter (fun v => v.val<k)

@[simp] theorem mem_prefix {n k : ℕ} {v : Vertex n} : v∈vertexPrefix n k ↔ v.val<k := by
  simp [vertexPrefix]

theorem prefix_card (n k : ℕ) (hk : k≤n+4) : (vertexPrefix n k).card=k := by
  rw [vertexPrefix,Fin.card_filter_val_lt,Nat.min_eq_right hk]

theorem prefix_four_clique (n : ℕ) : (graph n).IsClique (vertexPrefix n 4) := by
  intro u hu v hv huv
  have hu' := mem_prefix.mp hu
  have hv' := mem_prefix.mp hv
  change u≠v ∧ _
  refine ⟨huv,?_⟩
  have hne : u.val≠v.val := fun h => huv (Fin.ext h)
  omega

theorem prefix_step {n k : ℕ} (hk : k<n+4) :
    vertexPrefix n (k+1)=insert (⟨k,hk⟩ : Vertex n) (vertexPrefix n k) := by
  ext v
  simp only [mem_prefix,mem_insert,Fin.ext_iff]
  omega

def attachmentTriangle (n k : ℕ) (hk : k<n+4) : Finset (Vertex n) :=
  {hubA n,hubB n,⟨k-1,by omega⟩}

theorem attachmentTriangle_card {n k : ℕ} (hk0 : 4≤k) (hk : k<n+4) :
    (attachmentTriangle n k hk).card=3 := by
  simp [attachmentTriangle,hubA,hubB,Fin.ext_iff,show k-1≠0 by omega,
    show k-1≠1 by omega,show 0≠k-1 by omega,show 1≠k-1 by omega]

theorem attachmentTriangle_subset {n k : ℕ} (hk0 : 4≤k) (hk : k<n+4) :
    attachmentTriangle n k hk⊆vertexPrefix n k := by
  intro v hv
  simp only [attachmentTriangle,mem_insert,mem_singleton] at hv
  rcases hv with rfl | rfl | rfl <;> simp only [mem_prefix,hubA,hubB] <;> omega

theorem attachmentTriangle_clique {n k : ℕ} (hk0 : 4≤k) (hk : k<n+4) :
    (inducedOn (graph n) (vertexPrefix n k)).IsClique (attachmentTriangle n k hk) := by
  intro u hu v hv huv
  refine ⟨?_,attachmentTriangle_subset hk0 hk hu,attachmentTriangle_subset hk0 hk hv⟩
  change u∈attachmentTriangle n k hk at hu
  change v∈attachmentTriangle n k hk at hv
  simp only [attachmentTriangle,mem_insert,mem_singleton] at hu hv
  change u≠v ∧ _
  refine ⟨huv,?_⟩
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    simp only [hubA,hubB] at * <;> try omega
  exact (huv rfl).elim

theorem induced_prefix_step {n k : ℕ} (hk0 : 4≤k) (hk : k<n+4) :
    inducedOn (graph n) (vertexPrefix n (k+1))=
      inducedOn (graph n) (vertexPrefix n k) ⊔ attachmentStar (⟨k,hk⟩ : Vertex n)
        (attachmentTriangle n k hk) := by
  ext u v
  change ((u≠v ∧ (u.val<2 ∨ v.val<2 ∨ u.val+1=v.val ∨ v.val+1=u.val)) ∧
      u∈vertexPrefix n (k+1) ∧ v∈vertexPrefix n (k+1)) ↔
    ((u≠v ∧ (u.val<2 ∨ v.val<2 ∨ u.val+1=v.val ∨ v.val+1=u.val)) ∧
      u∈vertexPrefix n k ∧ v∈vertexPrefix n k) ∨
    (u≠v ∧ ((u=⟨k,hk⟩ ∧ v∈attachmentTriangle n k hk) ∨
      (v=⟨k,hk⟩ ∧ u∈attachmentTriangle n k hk)))
  simp only [mem_prefix,attachmentTriangle,mem_insert,mem_singleton,ne_eq,Fin.ext_iff,hubA,hubB]
  omega

theorem prefix_threeTree (n t : ℕ) (ht : t≤n) :
    ThreeTreeOn (vertexPrefix n (t+4)) (inducedOn (graph n) (vertexPrefix n (t+4))) := by
  induction t with
  | zero =>
      rw [Nat.zero_add,inducedOn_clique (prefix_four_clique n)]
      exact ThreeTreeOn.tetrahedron _ (prefix_card n 4 (by omega))
  | succ t ih =>
      have hk : t+4<n+4 := by omega
      have hs := ThreeTreeOn.attach (ih (by omega)) (⟨t+4,hk⟩ : Vertex n)
        (by simp) (attachmentTriangle n (t+4) hk) (attachmentTriangle_card (by omega) hk)
        (attachmentTriangle_subset (by omega) hk) (attachmentTriangle_clique (by omega) hk)
      have he : t+1+4=(t+4)+1 := by omega
      simpa only [Nat.succ_eq_add_one,he,←prefix_step hk,←induced_prefix_step (by omega) hk] using hs

theorem graph_isThreeTree (n : ℕ) : IsThreeTree (graph n) := by
  have h := prefix_threeTree n n le_rfl
  have hp : vertexPrefix n (n+4)=univ := by ext v; simp [mem_prefix,v.isLt]
  rw [hp] at h
  have he : inducedOn (graph n) univ=graph n := by ext u v; simp [inducedOn]
  rwa [he] at h

theorem tetrahedra_contain_hubs {n : ℕ} {C : Finset (Vertex n)}
    (hC : C∈tetrahedra (graph n)) : {hubA n,hubB n}⊆C := by
  simp only [tetrahedra,mem_filter,mem_univ,true_and] at hC
  obtain ⟨hc,hcl⟩ := hC
  obtain ⟨s,hs⟩ := clique_covers C ⟨by omega,hcl⟩
  rw [←hs] at hc ⊢
  rcases s with u | ⟨r,i⟩ | ⟨r,i⟩
  · simp [clique]
  · fin_cases r <;> simp [clique] at hc
  · fin_cases r <;> simp [clique,Finset.card_pair (vertex_left_ne_right i)] at hc ⊢

theorem tetrahedra_hub_filter (n : ℕ) :
    (tetrahedra (graph n)).filter (fun C => ({hubA n,hubB n} : Finset (Vertex n))⊆C)=
      tetrahedra (graph n) := by
  apply filter_eq_self.mpr
  intro C hC
  exact tetrahedra_contain_hubs hC

theorem tetrahedra_count (n : ℕ) : (tetrahedra (graph n)).card=n+1 := by
  have h := (graph_isThreeTree n).tetrahedra_card
  simp only [card_univ,Fintype.card_fin] at h
  omega

end GraphicalZonotopes.PathJoin
