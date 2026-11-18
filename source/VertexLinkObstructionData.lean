module
prelude
public import ConcreteGrowth
public import Init.Data.List.Nat.Sum

@[expose] public section

/-!
# Exact vertex-link obstruction records

These are the four terminal families of the complete graph-conditioned
search whose vertex-link Euler equation fails. Every cell retains its
literal vertex, edge and ridge masks. The finite checks below use only
kernel reduction of lists and natural numbers.
-/

namespace Papers.RationalityTen.VertexLinkObstructionData

open ConcreteGrowth

/-- Remove repeated edge masks; this definition has a simple membership
and no-duplicate proof, independent of the computation backend. -/
def distinct : List Nat → List Nat
  | [] => []
  | a :: tail => if a ∈ tail then distinct tail else a :: distinct tail

@[simp] theorem mem_distinct {a : Nat} (values : List Nat) :
    a ∈ distinct values ↔ a ∈ values := by
  induction values with
  | nil => simp [distinct]
  | cons b tail ih =>
    by_cases hb : b ∈ tail
    · simp only [distinct, if_pos hb, ih, List.mem_cons]
      exact ⟨Or.inr, fun h => h.elim (fun h => h.symm ▸ hb) id⟩
    · simp [distinct, hb, ih]

theorem distinct_nodup (values : List Nat) : (distinct values).Nodup := by
  induction values with
  | nil => exact List.nodup_nil
  | cons a tail ih =>
    by_cases ha : a ∈ tail
    · simpa only [distinct, if_pos ha] using ih
    · simp only [distinct, if_neg ha, List.nodup_cons, mem_distinct]
      exact ⟨ha, ih⟩

def degree (cell : Cell) (vertex : Nat) : Nat :=
  ((distinct cell.edges).filter fun edge => edge.testBit vertex).length

def weight (cell : Cell) (vertex : Nat) : Nat :=
  if cell.vertices.testBit vertex then degree cell vertex - 2 else 0

def weightSum (cells : List Cell) (vertex : Nat) : Nat :=
  (cells.map fun cell => weight cell vertex).sum

noncomputable def graphDegree (cells : List Cell) (vertex : Nat) : Nat :=
  ((distinct (cells.flatMap Cell.edges)).filter fun edge => edge.testBit vertex).length

noncomputable def check (cells : List Cell) (vertex : Nat) : Bool :=
  decide (weightSum cells vertex + 4 ≠ 2 * graphDegree cells vertex)

/-- row31_m16_e10_q1.jsonl.gz, graph 477, terminal 0. -/
def G0477T0 : List Cell :=
  [⟨1,43,[3,9,10,33,34,40],[11,35,41,42]⟩,
   ⟨1,75,[3,9,10,65,66,72],[11,67,73,74]⟩,
   ⟨1,29,[5,9,12,17,20,24],[13,21,25,28]⟩,
   ⟨1,105,[9,33,40,65,72,96],[41,73,97,104]⟩,
   ⟨1,150,[6,18,20,130,132,144],[22,134,146,148]⟩,
   ⟨1,106,[10,34,40,66,72,96],[42,74,98,104]⟩,
   ⟨2,675,[3,33,34,129,130,160,513,514,640],[35,161,162,515,641,642]⟩,
   ⟨2,835,[3,65,66,257,258,320,513,514,768],[67,321,322,515,769,770]⟩,
   ⟨3,781,[5,9,12,257,260,513,520,768],[13,261,521,769,780]⟩,
   ⟨2,181,[5,17,20,33,36,129,132,144,160],[21,37,145,148,161,164]⟩,
   ⟨2,357,[5,33,36,65,68,96,257,260,320],[37,97,100,261,321,324]⟩,
   ⟨2,665,[9,17,24,129,144,513,520,528,640],[25,145,521,536,641,656]⟩,
   ⟨2,342,[6,18,20,66,68,258,260,272,320],[22,70,274,276,322,324]⟩,
   ⟨2,230,[6,34,36,66,68,96,130,132,160],[70,98,100,134,162,164]⟩,
   ⟨2,914,[18,130,144,258,272,514,528,640,768],[146,274,642,656,770,784]⟩,
   ⟨3,796,[12,20,24,260,272,520,528,768],[28,276,536,780,784]⟩]

theorem G0477T0_weight : weightSum G0477T0 0 + 4 = 20 := by decide +kernel
theorem G0477T0_degree : 2 * graphDegree G0477T0 0 = 18 := by decide +kernel
theorem G0477T0_checked : check G0477T0 0 = true := by decide +kernel

/-- row31_m16_e10_q1.jsonl.gz, graph 811, terminal 0. -/
def G0811T0 : List Cell :=
  [⟨1,85,[5,17,20,65,68,80],[21,69,81,84]⟩,
   ⟨1,197,[5,65,68,129,132,192],[69,133,193,196]⟩,
   ⟨1,209,[17,65,80,129,144,192],[81,145,193,208]⟩,
   ⟨1,609,[33,65,96,513,544,576],[97,545,577,608]⟩,
   ⟨1,30,[6,10,12,18,20,24],[14,22,26,28]⟩,
   ⟨1,212,[20,68,80,132,144,192],[84,148,196,208]⟩,
   ⟨2,403,[3,17,18,129,130,144,257,258,272],[131,145,146,259,273,274]⟩,
   ⟨2,675,[3,33,34,129,130,160,513,514,544],[131,161,162,515,545,546]⟩,
   ⟨2,835,[3,65,257,258,320,513,514,576,768],[259,321,515,577,770,832]⟩,
   ⟨2,285,[5,9,12,17,20,24,257,264,272],[13,21,28,265,273,280]⟩,
   ⟨2,173,[5,9,12,33,36,40,129,132,160],[13,41,44,133,161,164]⟩,
   ⟨3,361,[9,33,40,65,96,257,264,320],[41,97,265,321,360]⟩,
   ⟨2,558,[6,10,12,34,36,40,514,520,544],[14,38,44,522,546,552]⟩,
   ⟨2,182,[6,18,20,34,36,130,132,144,160],[22,38,146,148,162,164]⟩,
   ⟨2,794,[10,18,24,258,264,272,514,520,768],[26,274,280,522,770,776]⟩,
   ⟨3,872,[40,96,264,320,520,544,576,768],[360,552,608,776,832]⟩]

theorem G0811T0_weight : weightSum G0811T0 0 + 4 = 20 := by decide +kernel
theorem G0811T0_degree : 2 * graphDegree G0811T0 0 = 18 := by decide +kernel
theorem G0811T0_checked : check G0811T0 0 = true := by decide +kernel

/-- row31_m16_e10_q1.jsonl.gz, graph 1439, terminal 0. -/
def G1439T0 : List Cell :=
  [⟨1,275,[3,17,18,257,258,272],[19,259,273,274]⟩,
   ⟨1,29,[5,9,12,17,20,24],[13,21,25,28]⟩,
   ⟨1,53,[5,17,20,33,36,48],[21,37,49,52]⟩,
   ⟨1,57,[9,17,24,33,40,48],[25,41,49,56]⟩,
   ⟨1,298,[10,34,40,258,264,288],[42,266,290,296]⟩,
   ⟨1,60,[12,20,24,36,40,48],[28,44,52,56]⟩,
   ⟨2,659,[3,17,18,129,130,144,513,514,640],[19,145,146,515,641,642]⟩,
   ⟨2,803,[3,33,34,257,258,288,513,514,544],[259,289,290,515,545,546]⟩,
   ⟨2,205,[5,9,12,65,68,72,129,132,192],[13,73,76,133,193,196]⟩,
   ⟨2,677,[5,33,36,129,132,513,516,544,640],[37,133,545,548,641,644]⟩,
   ⟨2,361,[9,33,40,65,72,257,264,288,320],[41,73,289,296,321,328]⟩,
   ⟨3,465,[17,65,129,144,192,257,272,320],[145,193,273,321,464]⟩,
   ⟨2,558,[6,10,12,34,36,40,514,516,544],[14,42,44,518,546,548]⟩,
   ⟨2,334,[6,10,12,66,68,72,258,264,320],[14,70,76,266,322,328]⟩,
   ⟨2,710,[6,66,68,130,132,192,514,516,640],[70,194,196,518,642,644]⟩,
   ⟨3,466,[18,66,130,144,192,258,272,320],[146,194,274,322,464]⟩]

theorem G1439T0_weight : weightSum G1439T0 0 + 4 = 20 := by decide +kernel
theorem G1439T0_degree : 2 * graphDegree G1439T0 0 = 18 := by decide +kernel
theorem G1439T0_checked : check G1439T0 0 = true := by decide +kernel

/-- row31_m16_e10_q1.jsonl.gz, graph 1627, terminal 0. -/
def G1627T0 : List Cell :=
  [⟨1,139,[3,9,10,129,130,136],[11,131,137,138]⟩,
   ⟨1,267,[3,9,10,257,258,264],[11,259,265,266]⟩,
   ⟨1,45,[5,9,12,33,36,40],[13,37,41,44]⟩,
   ⟨1,393,[9,129,136,257,264,384],[137,265,385,392]⟩,
   ⟨1,582,[6,66,68,514,516,576],[70,518,578,580]⟩,
   ⟨1,394,[10,130,136,258,264,384],[138,266,386,392]⟩,
   ⟨2,675,[3,33,34,129,130,160,513,514,544],[131,161,162,515,545,546]⟩,
   ⟨2,835,[3,65,66,257,258,320,513,514,576],[259,321,322,515,577,578]⟩,
   ⟨2,93,[5,9,12,17,20,65,68,72,80],[13,21,73,76,81,84]⟩,
   ⟨2,181,[5,17,20,33,36,48,129,144,160],[21,37,52,145,161,176]⟩,
   ⟨3,617,[9,33,40,65,72,513,544,576],[41,73,545,577,616]⟩,
   ⟨2,465,[17,65,80,129,144,257,272,320,384],[81,145,321,336,385,400]⟩,
   ⟨2,566,[6,18,20,34,36,48,514,516,544],[22,50,52,518,546,548]⟩,
   ⟨2,342,[6,18,20,66,68,80,258,272,320],[22,70,84,274,322,336]⟩,
   ⟨2,434,[18,34,48,130,144,160,258,272,384],[50,162,176,274,386,400]⟩,
   ⟨3,620,[12,36,40,68,72,516,544,576],[44,76,548,580,616]⟩]

theorem G1627T0_weight : weightSum G1627T0 0 + 4 = 20 := by decide +kernel
theorem G1627T0_degree : 2 * graphDegree G1627T0 0 = 18 := by decide +kernel
theorem G1627T0_checked : check G1627T0 0 = true := by decide +kernel

#print axioms G0477T0_checked
#print axioms G0811T0_checked
#print axioms G1439T0_checked
#print axioms G1627T0_checked

end Papers.RationalityTen.VertexLinkObstructionData
