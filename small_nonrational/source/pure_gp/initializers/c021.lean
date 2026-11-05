module
prelude
public import PureGP.SupportCore
public import PureGP.Cases.C021

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Papers.RationalityTen.PureGP.Initializers.C021
/- Finite consequence of support-sign equations; their actual geometry is separate. -/
def anchor : Nat := 6
def globalNegation : Bool := Bool.false
def edgeTable : Table SupportEdge := (Table.node 110 (Table.node 55 (Table.node 27 (Table.node 13 (Table.node 6 (Table.node 3 (Table.node 1 (Table.leaf (SupportEdge.mk 6 21 Bool.false)) (Table.node 2 (Table.leaf (SupportEdge.mk 6 36 Bool.false)) (Table.leaf (SupportEdge.mk 6 37 Bool.false)))) (Table.node 4 (Table.leaf (SupportEdge.mk 6 39 Bool.false)) (Table.node 5 (Table.leaf (SupportEdge.mk 9 24 Bool.false)) (Table.leaf (SupportEdge.mk 9 41 Bool.true))))) (Table.node 9 (Table.node 7 (Table.leaf (SupportEdge.mk 9 43 Bool.true)) (Table.node 8 (Table.leaf (SupportEdge.mk 9 45 Bool.false)) (Table.leaf (SupportEdge.mk 13 28 Bool.false)))) (Table.node 11 (Table.node 10 (Table.leaf (SupportEdge.mk 13 47 Bool.true)) (Table.leaf (SupportEdge.mk 13 49 Bool.true))) (Table.node 12 (Table.leaf (SupportEdge.mk 13 51 Bool.false)) (Table.leaf (SupportEdge.mk 73 93 Bool.false)))))) (Table.node 20 (Table.node 16 (Table.node 14 (Table.leaf (SupportEdge.mk 73 112 Bool.false)) (Table.node 15 (Table.leaf (SupportEdge.mk 73 114 Bool.false)) (Table.leaf (SupportEdge.mk 73 116 Bool.true)))) (Table.node 18 (Table.node 17 (Table.leaf (SupportEdge.mk 143 163 Bool.false)) (Table.leaf (SupportEdge.mk 143 182 Bool.false))) (Table.node 19 (Table.leaf (SupportEdge.mk 143 184 Bool.false)) (Table.leaf (SupportEdge.mk 143 186 Bool.true))))) (Table.node 23 (Table.node 21 (Table.leaf (SupportEdge.mk 6 56 Bool.true)) (Table.node 22 (Table.leaf (SupportEdge.mk 6 71 Bool.true)) (Table.leaf (SupportEdge.mk 6 72 Bool.true)))) (Table.node 25 (Table.node 24 (Table.leaf (SupportEdge.mk 6 73 Bool.true)) (Table.leaf (SupportEdge.mk 10 60 Bool.true))) (Table.node 26 (Table.leaf (SupportEdge.mk 10 77 Bool.false)) (Table.leaf (SupportEdge.mk 10 79 Bool.false))))))) (Table.node 41 (Table.node 34 (Table.node 30 (Table.node 28 (Table.leaf (SupportEdge.mk 10 80 Bool.false)) (Table.node 29 (Table.leaf (SupportEdge.mk 14 64 Bool.true)) (Table.leaf (SupportEdge.mk 14 83 Bool.false)))) (Table.node 32 (Table.node 31 (Table.leaf (SupportEdge.mk 14 85 Bool.false)) (Table.leaf (SupportEdge.mk 14 86 Bool.false))) (Table.node 33 (Table.leaf (SupportEdge.mk 39 94 Bool.false)) (Table.leaf (SupportEdge.mk 39 113 Bool.false))))) (Table.node 37 (Table.node 35 (Table.leaf (SupportEdge.mk 39 115 Bool.false)) (Table.node 36 (Table.leaf (SupportEdge.mk 39 116 Bool.false)) (Table.leaf (SupportEdge.mk 144 199 Bool.true)))) (Table.node 39 (Table.node 38 (Table.leaf (SupportEdge.mk 144 218 Bool.true)) (Table.leaf (SupportEdge.mk 144 220 Bool.true))) (Table.node 40 (Table.leaf (SupportEdge.mk 144 221 Bool.true)) (Table.leaf (SupportEdge.mk 7 57 Bool.true)))))) (Table.node 48 (Table.node 44 (Table.node 42 (Table.leaf (SupportEdge.mk 7 71 Bool.false)) (Table.node 43 (Table.leaf (SupportEdge.mk 7 75 Bool.true)) (Table.leaf (SupportEdge.mk 7 77 Bool.true)))) (Table.node 46 (Table.node 45 (Table.leaf (SupportEdge.mk 9 59 Bool.true)) (Table.leaf (SupportEdge.mk 9 73 Bool.false))) (Table.node 47 (Table.leaf (SupportEdge.mk 9 78 Bool.false)) (Table.leaf (SupportEdge.mk 9 80 Bool.true))))) (Table.node 51 (Table.node 49 (Table.leaf (SupportEdge.mk 16 66 Bool.true)) (Table.node 50 (Table.leaf (SupportEdge.mk 16 82 Bool.true)) (Table.leaf (SupportEdge.mk 16 87 Bool.false)))) (Table.node 53 (Table.node 52 (Table.leaf (SupportEdge.mk 16 89 Bool.true)) (Table.leaf (SupportEdge.mk 41 96 Bool.false))) (Table.node 54 (Table.leaf (SupportEdge.mk 41 112 Bool.true)) (Table.leaf (SupportEdge.mk 41 117 Bool.false)))))))) (Table.node 82 (Table.node 68 (Table.node 61 (Table.node 58 (Table.node 56 (Table.leaf (SupportEdge.mk 41 119 Bool.true)) (Table.node 57 (Table.leaf (SupportEdge.mk 146 201 Bool.true)) (Table.leaf (SupportEdge.mk 146 217 Bool.false)))) (Table.node 59 (Table.leaf (SupportEdge.mk 146 222 Bool.true)) (Table.node 60 (Table.leaf (SupportEdge.mk 146 224 Bool.false)) (Table.leaf (SupportEdge.mk 15 65 Bool.true))))) (Table.node 64 (Table.node 62 (Table.leaf (SupportEdge.mk 15 75 Bool.true)) (Table.node 63 (Table.leaf (SupportEdge.mk 15 81 Bool.true)) (Table.leaf (SupportEdge.mk 15 87 Bool.true)))) (Table.node 66 (Table.node 65 (Table.leaf (SupportEdge.mk 17 67 Bool.true)) (Table.leaf (SupportEdge.mk 17 77 Bool.true))) (Table.node 67 (Table.leaf (SupportEdge.mk 17 83 Bool.true)) (Table.leaf (SupportEdge.mk 17 89 Bool.false)))))) (Table.node 75 (Table.node 71 (Table.node 69 (Table.leaf (SupportEdge.mk 19 69 Bool.true)) (Table.node 70 (Table.leaf (SupportEdge.mk 19 79 Bool.true)) (Table.leaf (SupportEdge.mk 19 85 Bool.true)))) (Table.node 73 (Table.node 72 (Table.leaf (SupportEdge.mk 19 90 Bool.false)) (Table.leaf (SupportEdge.mk 53 108 Bool.false))) (Table.node 74 (Table.leaf (SupportEdge.mk 53 118 Bool.false)) (Table.leaf (SupportEdge.mk 53 122 Bool.false))))) (Table.node 78 (Table.node 76 (Table.leaf (SupportEdge.mk 53 125 Bool.false)) (Table.node 77 (Table.leaf (SupportEdge.mk 158 213 Bool.true)) (Table.leaf (SupportEdge.mk 158 223 Bool.true)))) (Table.node 80 (Table.node 79 (Table.leaf (SupportEdge.mk 158 227 Bool.true)) (Table.leaf (SupportEdge.mk 158 230 Bool.true))) (Table.node 81 (Table.leaf (SupportEdge.mk 26 61 Bool.false)) (Table.leaf (SupportEdge.mk 26 91 Bool.true))))))) (Table.node 96 (Table.node 89 (Table.node 85 (Table.node 83 (Table.leaf (SupportEdge.mk 26 101 Bool.true)) (Table.node 84 (Table.leaf (SupportEdge.mk 26 102 Bool.true)) (Table.leaf (SupportEdge.mk 29 64 Bool.false)))) (Table.node 87 (Table.node 86 (Table.leaf (SupportEdge.mk 29 94 Bool.true)) (Table.leaf (SupportEdge.mk 29 105 Bool.false))) (Table.node 88 (Table.leaf (SupportEdge.mk 29 106 Bool.false)) (Table.leaf (SupportEdge.mk 32 67 Bool.false))))) (Table.node 92 (Table.node 90 (Table.leaf (SupportEdge.mk 32 97 Bool.true)) (Table.node 91 (Table.leaf (SupportEdge.mk 32 108 Bool.false)) (Table.leaf (SupportEdge.mk 32 109 Bool.false)))) (Table.node 94 (Table.node 93 (Table.leaf (SupportEdge.mk 48 83 Bool.false)) (Table.leaf (SupportEdge.mk 48 113 Bool.false))) (Table.node 95 (Table.leaf (SupportEdge.mk 48 122 Bool.false)) (Table.leaf (SupportEdge.mk 48 123 Bool.false)))))) (Table.node 103 (Table.node 99 (Table.node 97 (Table.leaf (SupportEdge.mk 173 208 Bool.false)) (Table.node 98 (Table.leaf (SupportEdge.mk 173 233 Bool.true)) (Table.leaf (SupportEdge.mk 173 242 Bool.true)))) (Table.node 101 (Table.node 100 (Table.leaf (SupportEdge.mk 173 243 Bool.true)) (Table.leaf (SupportEdge.mk 47 82 Bool.false))) (Table.node 102 (Table.leaf (SupportEdge.mk 47 102 Bool.false)) (Table.leaf (SupportEdge.mk 47 112 Bool.false))))) (Table.node 106 (Table.node 104 (Table.leaf (SupportEdge.mk 47 121 Bool.false)) (Table.node 105 (Table.leaf (SupportEdge.mk 47 123 Bool.true)) (Table.leaf (SupportEdge.mk 18 138 Bool.false)))) (Table.node 108 (Table.node 107 (Table.leaf (SupportEdge.mk 18 148 Bool.false)) (Table.leaf (SupportEdge.mk 18 154 Bool.false))) (Table.node 109 (Table.leaf (SupportEdge.mk 18 157 Bool.false)) (Table.leaf (SupportEdge.mk 19 139 Bool.false))))))))) (Table.node 165 (Table.node 137 (Table.node 123 (Table.node 116 (Table.node 113 (Table.node 111 (Table.leaf (SupportEdge.mk 19 149 Bool.false)) (Table.node 112 (Table.leaf (SupportEdge.mk 19 155 Bool.false)) (Table.leaf (SupportEdge.mk 19 158 Bool.false)))) (Table.node 114 (Table.leaf (SupportEdge.mk 20 140 Bool.false)) (Table.node 115 (Table.leaf (SupportEdge.mk 20 150 Bool.false)) (Table.leaf (SupportEdge.mk 20 156 Bool.false))))) (Table.node 119 (Table.node 117 (Table.leaf (SupportEdge.mk 20 159 Bool.false)) (Table.node 118 (Table.leaf (SupportEdge.mk 55 180 Bool.true)) (Table.leaf (SupportEdge.mk 55 190 Bool.true)))) (Table.node 121 (Table.node 120 (Table.leaf (SupportEdge.mk 55 194 Bool.true)) (Table.leaf (SupportEdge.mk 55 195 Bool.true))) (Table.node 122 (Table.leaf (SupportEdge.mk 90 215 Bool.true)) (Table.leaf (SupportEdge.mk 90 225 Bool.true)))))) (Table.node 130 (Table.node 126 (Table.node 124 (Table.leaf (SupportEdge.mk 90 229 Bool.true)) (Table.node 125 (Table.leaf (SupportEdge.mk 90 230 Bool.true)) (Table.leaf (SupportEdge.mk 21 126 Bool.true)))) (Table.node 128 (Table.node 127 (Table.leaf (SupportEdge.mk 21 161 Bool.false)) (Table.leaf (SupportEdge.mk 21 162 Bool.false))) (Table.node 129 (Table.leaf (SupportEdge.mk 21 163 Bool.false)) (Table.leaf (SupportEdge.mk 25 130 Bool.true))))) (Table.node 133 (Table.node 131 (Table.leaf (SupportEdge.mk 25 167 Bool.true)) (Table.node 132 (Table.leaf (SupportEdge.mk 25 169 Bool.true)) (Table.leaf (SupportEdge.mk 25 170 Bool.true)))) (Table.node 135 (Table.node 134 (Table.leaf (SupportEdge.mk 29 134 Bool.true)) (Table.leaf (SupportEdge.mk 29 173 Bool.true))) (Table.node 136 (Table.leaf (SupportEdge.mk 29 175 Bool.true)) (Table.leaf (SupportEdge.mk 29 176 Bool.true))))))) (Table.node 151 (Table.node 144 (Table.node 140 (Table.node 138 (Table.leaf (SupportEdge.mk 39 144 Bool.true)) (Table.node 139 (Table.leaf (SupportEdge.mk 39 183 Bool.true)) (Table.leaf (SupportEdge.mk 39 185 Bool.true)))) (Table.node 142 (Table.node 141 (Table.leaf (SupportEdge.mk 39 186 Bool.true)) (Table.leaf (SupportEdge.mk 94 199 Bool.false))) (Table.node 143 (Table.leaf (SupportEdge.mk 94 233 Bool.true)) (Table.leaf (SupportEdge.mk 94 235 Bool.true))))) (Table.node 147 (Table.node 145 (Table.leaf (SupportEdge.mk 94 236 Bool.true)) (Table.node 146 (Table.leaf (SupportEdge.mk 27 132 Bool.true)) (Table.leaf (SupportEdge.mk 27 162 Bool.false)))) (Table.node 149 (Table.node 148 (Table.leaf (SupportEdge.mk 27 171 Bool.true)) (Table.leaf (SupportEdge.mk 27 175 Bool.false))) (Table.node 150 (Table.leaf (SupportEdge.mk 28 133 Bool.true)) (Table.leaf (SupportEdge.mk 28 163 Bool.false)))))) (Table.node 158 (Table.node 154 (Table.node 152 (Table.leaf (SupportEdge.mk 28 172 Bool.true)) (Table.node 153 (Table.leaf (SupportEdge.mk 28 176 Bool.false)) (Table.leaf (SupportEdge.mk 33 138 Bool.true)))) (Table.node 156 (Table.node 155 (Table.leaf (SupportEdge.mk 33 168 Bool.false)) (Table.leaf (SupportEdge.mk 33 177 Bool.false))) (Table.node 157 (Table.leaf (SupportEdge.mk 33 180 Bool.false)) (Table.leaf (SupportEdge.mk 49 154 Bool.true))))) (Table.node 161 (Table.node 159 (Table.leaf (SupportEdge.mk 49 184 Bool.true)) (Table.node 160 (Table.leaf (SupportEdge.mk 49 191 Bool.false)) (Table.leaf (SupportEdge.mk 49 194 Bool.false)))) (Table.node 163 (Table.node 162 (Table.leaf (SupportEdge.mk 104 209 Bool.false)) (Table.leaf (SupportEdge.mk 104 234 Bool.true))) (Table.node 164 (Table.leaf (SupportEdge.mk 104 241 Bool.false)) (Table.leaf (SupportEdge.mk 104 244 Bool.false)))))))) (Table.node 192 (Table.node 178 (Table.node 171 (Table.node 168 (Table.node 166 (Table.leaf (SupportEdge.mk 30 135 Bool.true)) (Table.node 167 (Table.leaf (SupportEdge.mk 30 165 Bool.false)) (Table.leaf (SupportEdge.mk 30 171 Bool.false)))) (Table.node 169 (Table.leaf (SupportEdge.mk 30 177 Bool.false)) (Table.node 170 (Table.leaf (SupportEdge.mk 32 137 Bool.true)) (Table.leaf (SupportEdge.mk 32 167 Bool.false))))) (Table.node 174 (Table.node 172 (Table.leaf (SupportEdge.mk 32 173 Bool.false)) (Table.node 173 (Table.leaf (SupportEdge.mk 32 179 Bool.true)) (Table.leaf (SupportEdge.mk 34 139 Bool.true)))) (Table.node 176 (Table.node 175 (Table.leaf (SupportEdge.mk 34 169 Bool.false)) (Table.leaf (SupportEdge.mk 34 175 Bool.false))) (Table.node 177 (Table.leaf (SupportEdge.mk 34 180 Bool.true)) (Table.leaf (SupportEdge.mk 53 158 Bool.true)))))) (Table.node 185 (Table.node 181 (Table.node 179 (Table.leaf (SupportEdge.mk 53 188 Bool.true)) (Table.node 180 (Table.leaf (SupportEdge.mk 53 192 Bool.true)) (Table.leaf (SupportEdge.mk 53 195 Bool.true)))) (Table.node 183 (Table.node 182 (Table.leaf (SupportEdge.mk 108 213 Bool.false)) (Table.leaf (SupportEdge.mk 108 238 Bool.true))) (Table.node 184 (Table.leaf (SupportEdge.mk 108 242 Bool.true)) (Table.leaf (SupportEdge.mk 108 245 Bool.true))))) (Table.node 188 (Table.node 186 (Table.leaf (SupportEdge.mk 45 150 Bool.true)) (Table.node 187 (Table.leaf (SupportEdge.mk 45 170 Bool.true)) (Table.leaf (SupportEdge.mk 45 186 Bool.false)))) (Table.node 190 (Table.node 189 (Table.leaf (SupportEdge.mk 45 189 Bool.false)) (Table.leaf (SupportEdge.mk 45 190 Bool.false))) (Table.node 191 (Table.leaf (SupportEdge.mk 65 135 Bool.false)) (Table.leaf (SupportEdge.mk 65 200 Bool.false))))))) (Table.node 206 (Table.node 199 (Table.node 195 (Table.node 193 (Table.leaf (SupportEdge.mk 65 206 Bool.false)) (Table.node 194 (Table.leaf (SupportEdge.mk 65 213 Bool.false)) (Table.leaf (SupportEdge.mk 66 136 Bool.false)))) (Table.node 197 (Table.node 196 (Table.leaf (SupportEdge.mk 66 201 Bool.false)) (Table.leaf (SupportEdge.mk 66 207 Bool.false))) (Table.node 198 (Table.leaf (SupportEdge.mk 66 214 Bool.false)) (Table.leaf (SupportEdge.mk 68 138 Bool.false))))) (Table.node 202 (Table.node 200 (Table.leaf (SupportEdge.mk 68 203 Bool.false)) (Table.node 201 (Table.leaf (SupportEdge.mk 68 209 Bool.false)) (Table.leaf (SupportEdge.mk 68 215 Bool.false)))) (Table.node 204 (Table.node 203 (Table.leaf (SupportEdge.mk 87 157 Bool.false)) (Table.leaf (SupportEdge.mk 87 222 Bool.true))) (Table.node 205 (Table.leaf (SupportEdge.mk 87 226 Bool.true)) (Table.leaf (SupportEdge.mk 87 230 Bool.false)))))) (Table.node 213 (Table.node 209 (Table.node 207 (Table.leaf (SupportEdge.mk 107 177 Bool.false)) (Table.node 208 (Table.leaf (SupportEdge.mk 107 237 Bool.true)) (Table.leaf (SupportEdge.mk 107 241 Bool.true)))) (Table.node 211 (Table.node 210 (Table.leaf (SupportEdge.mk 107 245 Bool.false)) (Table.leaf (SupportEdge.mk 80 150 Bool.false))) (Table.node 212 (Table.leaf (SupportEdge.mk 80 205 Bool.true)) (Table.leaf (SupportEdge.mk 80 221 Bool.false))))) (Table.node 216 (Table.node 214 (Table.leaf (SupportEdge.mk 80 224 Bool.false)) (Table.node 215 (Table.leaf (SupportEdge.mk 80 225 Bool.false)) (Table.leaf (SupportEdge.mk 102 172 Bool.false)))) (Table.node 218 (Table.node 217 (Table.leaf (SupportEdge.mk 102 207 Bool.false)) (Table.leaf (SupportEdge.mk 102 232 Bool.true))) (Table.node 219 (Table.leaf (SupportEdge.mk 102 241 Bool.true)) (Table.leaf (SupportEdge.mk 102 243 Bool.false))))))))))
def edge (index : Nat) : SupportEdge := edgeTable.get index
def zeroTable : Table Nat := (Table.node 5 (Table.node 2 (Table.node 1 (Table.leaf 38) (Table.leaf 74)) (Table.node 3 (Table.leaf 76) (Table.node 4 (Table.leaf 88) (Table.leaf 103)))) (Table.node 7 (Table.node 6 (Table.leaf 160) (Table.leaf 164)) (Table.node 8 (Table.leaf 174) (Table.node 9 (Table.leaf 178) (Table.leaf 212)))))
def zero (index : Nat) : Nat := zeroTable.get index
def SupportEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 220 → (edge index).Holds assignment
def ZeroEquations (assignment : Nat → Sign) : Prop :=
  ∀ index, LT.lt index 10 → Eq (assignment (zero index)) Sign.zero

theorem initial_domains_sound (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment) :
    ∀ index, LT.lt index 252 →
      Eq ((Cases.C021.initial index).allows
        (Sign.withNegation globalNegation (assignment index))) Bool.true :=
  let hnode21 : Eq (assignment 21) Sign.positive :=
    Eq.trans (h_support 0 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode36 : Eq (assignment 36) Sign.positive :=
    Eq.trans (h_support 1 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode37 : Eq (assignment 37) Sign.positive :=
    Eq.trans (h_support 2 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode39 : Eq (assignment 39) Sign.positive :=
    Eq.trans (h_support 3 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) h_anchor)
  let hnode56 : Eq (assignment 56) Sign.negative :=
    Eq.trans (h_support 20 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode71 : Eq (assignment 71) Sign.negative :=
    Eq.trans (h_support 21 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode72 : Eq (assignment 72) Sign.negative :=
    Eq.trans (h_support 22 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode73 : Eq (assignment 73) Sign.negative :=
    Eq.trans (h_support 23 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) h_anchor)
  let hnode7 : Eq (assignment 7) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 41 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode71)
  let hnode9 : Eq (assignment 9) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 45 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode73)
  let hnode93 : Eq (assignment 93) Sign.negative :=
    Eq.trans (h_support 12 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode73)
  let hnode94 : Eq (assignment 94) Sign.positive :=
    Eq.trans (h_support 32 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode39)
  let hnode112 : Eq (assignment 112) Sign.negative :=
    Eq.trans (h_support 13 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode73)
  let hnode113 : Eq (assignment 113) Sign.positive :=
    Eq.trans (h_support 33 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode39)
  let hnode114 : Eq (assignment 114) Sign.negative :=
    Eq.trans (h_support 14 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode73)
  let hnode115 : Eq (assignment 115) Sign.positive :=
    Eq.trans (h_support 34 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode39)
  let hnode116 : Eq (assignment 116) Sign.positive :=
    Eq.trans (h_support 35 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode39)
  let hnode126 : Eq (assignment 126) Sign.negative :=
    Eq.trans (h_support 125 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode21)
  let hnode144 : Eq (assignment 144) Sign.negative :=
    Eq.trans (h_support 137 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode39)
  let hnode161 : Eq (assignment 161) Sign.positive :=
    Eq.trans (h_support 126 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode21)
  let hnode162 : Eq (assignment 162) Sign.positive :=
    Eq.trans (h_support 127 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode21)
  let hnode163 : Eq (assignment 163) Sign.positive :=
    Eq.trans (h_support 128 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode21)
  let hnode183 : Eq (assignment 183) Sign.negative :=
    Eq.trans (h_support 138 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode39)
  let hnode185 : Eq (assignment 185) Sign.negative :=
    Eq.trans (h_support 139 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode39)
  let hnode186 : Eq (assignment 186) Sign.negative :=
    Eq.trans (h_support 140 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode39)
  let hnode24 : Eq (assignment 24) Sign.negative :=
    Eq.trans (h_support 4 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode9)
  let hnode27 : Eq (assignment 27) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 146 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode162)
  let hnode28 : Eq (assignment 28) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 150 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode163)
  let hnode29 : Eq (assignment 29) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 85 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode94)
  let hnode41 : Eq (assignment 41) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 53 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode112)
  let hnode43 : Eq (assignment 43) Sign.positive :=
    Eq.trans (h_support 6 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode9)
  let hnode45 : Eq (assignment 45) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 187 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode186)
  let hnode47 : Eq (assignment 47) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 102 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode112)
  let hnode48 : Eq (assignment 48) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 93 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode113)
  let hnode57 : Eq (assignment 57) Sign.positive :=
    Eq.trans (h_support 40 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode7)
  let hnode59 : Eq (assignment 59) Sign.positive :=
    Eq.trans (h_support 44 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode9)
  let hnode75 : Eq (assignment 75) Sign.positive :=
    Eq.trans (h_support 42 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode7)
  let hnode77 : Eq (assignment 77) Sign.positive :=
    Eq.trans (h_support 43 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode7)
  let hnode78 : Eq (assignment 78) Sign.negative :=
    Eq.trans (h_support 46 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode9)
  let hnode80 : Eq (assignment 80) Sign.positive :=
    Eq.trans (h_support 47 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode9)
  let hnode143 : Eq (assignment 143) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 16 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode163)
  let hnode199 : Eq (assignment 199) Sign.positive :=
    Eq.trans (h_support 141 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode94)
  let hnode218 : Eq (assignment 218) Sign.positive :=
    Eq.trans (h_support 37 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode144)
  let hnode220 : Eq (assignment 220) Sign.positive :=
    Eq.trans (h_support 38 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode144)
  let hnode221 : Eq (assignment 221) Sign.positive :=
    Eq.trans (h_support 39 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode144)
  let hnode233 : Eq (assignment 233) Sign.negative :=
    Eq.trans (h_support 142 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode94)
  let hnode235 : Eq (assignment 235) Sign.negative :=
    Eq.trans (h_support 143 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode94)
  let hnode236 : Eq (assignment 236) Sign.negative :=
    Eq.trans (h_support 144 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode94)
  let hnode10 : Eq (assignment 10) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 25 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode77)
  let hnode13 : Eq (assignment 13) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 8 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode15 : Eq (assignment 15) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 61 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode75)
  let hnode17 : Eq (assignment 17) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 65 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode77)
  let hnode64 : Eq (assignment 64) Sign.negative :=
    Eq.trans (h_support 84 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode29)
  let hnode82 : Eq (assignment 82) Sign.negative :=
    Eq.trans (h_support 100 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode47)
  let hnode83 : Eq (assignment 83) Sign.positive :=
    Eq.trans (h_support 92 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode48)
  let hnode96 : Eq (assignment 96) Sign.positive :=
    Eq.trans (h_support 52 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode41)
  let hnode102 : Eq (assignment 102) Sign.negative :=
    Eq.trans (h_support 101 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode47)
  let hnode105 : Eq (assignment 105) Sign.negative :=
    Eq.trans (h_support 86 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode29)
  let hnode106 : Eq (assignment 106) Sign.negative :=
    Eq.trans (h_support 87 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode29)
  let hnode117 : Eq (assignment 117) Sign.positive :=
    Eq.trans (h_support 54 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode41)
  let hnode119 : Eq (assignment 119) Sign.negative :=
    Eq.trans (h_support 55 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode41)
  let hnode121 : Eq (assignment 121) Sign.negative :=
    Eq.trans (h_support 103 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode47)
  let hnode122 : Eq (assignment 122) Sign.positive :=
    Eq.trans (h_support 94 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode48)
  let hnode123 : Eq (assignment 123) Sign.positive :=
    Eq.trans (h_support 95 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode48)
  let hnode132 : Eq (assignment 132) Sign.negative :=
    Eq.trans (h_support 145 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode27)
  let hnode133 : Eq (assignment 133) Sign.negative :=
    Eq.trans (h_support 149 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode28)
  let hnode134 : Eq (assignment 134) Sign.positive :=
    Eq.trans (h_support 133 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode29)
  let hnode150 : Eq (assignment 150) Sign.positive :=
    Eq.trans (h_support 185 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode45)
  let hnode170 : Eq (assignment 170) Sign.positive :=
    Eq.trans (h_support 186 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode45)
  let hnode171 : Eq (assignment 171) Sign.negative :=
    Eq.trans (h_support 147 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode27)
  let hnode172 : Eq (assignment 172) Sign.negative :=
    Eq.trans (h_support 151 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode28)
  let hnode173 : Eq (assignment 173) Sign.positive :=
    Eq.trans (h_support 134 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode29)
  let hnode175 : Eq (assignment 175) Sign.positive :=
    Eq.trans (h_support 148 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode27)
  let hnode176 : Eq (assignment 176) Sign.positive :=
    Eq.trans (h_support 152 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode28)
  let hnode182 : Eq (assignment 182) Sign.positive :=
    Eq.trans (h_support 17 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode143)
  let hnode184 : Eq (assignment 184) Sign.positive :=
    Eq.trans (h_support 18 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode143)
  let hnode189 : Eq (assignment 189) Sign.negative :=
    Eq.trans (h_support 188 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode45)
  let hnode190 : Eq (assignment 190) Sign.negative :=
    Eq.trans (h_support 189 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode45)
  let hnode205 : Eq (assignment 205) Sign.negative :=
    Eq.trans (h_support 211 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode80)
  let hnode224 : Eq (assignment 224) Sign.positive :=
    Eq.trans (h_support 213 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode80)
  let hnode225 : Eq (assignment 225) Sign.positive :=
    Eq.trans (h_support 214 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode80)
  let hnode14 : Eq (assignment 14) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 28 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode64)
  let hnode16 : Eq (assignment 16) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 49 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode82)
  let hnode20 : Eq (assignment 20) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 114 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode150)
  let hnode25 : Eq (assignment 25) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 132 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode170)
  let hnode26 : Eq (assignment 26) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 83 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode102)
  let hnode30 : Eq (assignment 30) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 167 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode171)
  let hnode32 : Eq (assignment 32) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 171 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode173)
  let hnode34 : Eq (assignment 34) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 175 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode175)
  let hnode49 : Eq (assignment 49) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 158 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode184)
  let hnode51 : Eq (assignment 51) Sign.positive :=
    Eq.trans (h_support 11 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode13)
  let hnode53 : Eq (assignment 53) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 74 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode122)
  let hnode55 : Eq (assignment 55) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 118 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode190)
  let hnode60 : Eq (assignment 60) Sign.negative :=
    Eq.trans (h_support 24 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode10)
  let hnode65 : Eq (assignment 65) Sign.positive :=
    Eq.trans (h_support 60 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode15)
  let hnode67 : Eq (assignment 67) Sign.positive :=
    Eq.trans (h_support 64 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode17)
  let hnode79 : Eq (assignment 79) Sign.positive :=
    Eq.trans (h_support 26 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode10)
  let hnode81 : Eq (assignment 81) Sign.positive :=
    Eq.trans (h_support 62 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode15)
  let hnode87 : Eq (assignment 87) Sign.positive :=
    Eq.trans (h_support 63 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode15)
  let hnode89 : Eq (assignment 89) Sign.negative :=
    Eq.trans (h_support 67 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode17)
  let hnode90 : Eq (assignment 90) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 122 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode225)
  let hnode146 : Eq (assignment 146) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 59 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode224)
  let hnode207 : Eq (assignment 207) Sign.negative :=
    Eq.trans (h_support 216 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode102)
  let hnode208 : Eq (assignment 208) Sign.positive :=
    Eq.trans (h_support 96 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode173)
  let hnode232 : Eq (assignment 232) Sign.positive :=
    Eq.trans (h_support 217 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode102)
  let hnode241 : Eq (assignment 241) Sign.positive :=
    Eq.trans (h_support 218 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode102)
  let hnode242 : Eq (assignment 242) Sign.negative :=
    Eq.trans (h_support 98 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode173)
  let hnode243 : Eq (assignment 243) Sign.negative :=
    Eq.trans (h_support 99 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode173)
  let hnode19 : Eq (assignment 19) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 69 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode79)
  let hnode61 : Eq (assignment 61) Sign.positive :=
    Eq.trans (h_support 80 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode26)
  let hnode66 : Eq (assignment 66) Sign.negative :=
    Eq.trans (h_support 48 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode16)
  let hnode85 : Eq (assignment 85) Sign.positive :=
    Eq.trans (h_support 30 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode14)
  let hnode86 : Eq (assignment 86) Sign.positive :=
    Eq.trans (h_support 31 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode14)
  let hnode91 : Eq (assignment 91) Sign.negative :=
    Eq.trans (h_support 81 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode26)
  let hnode97 : Eq (assignment 97) Sign.negative :=
    Eq.trans (h_support 89 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode32)
  let hnode101 : Eq (assignment 101) Sign.negative :=
    Eq.trans (h_support 82 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode26)
  let hnode104 : Eq (assignment 104) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 163 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode241)
  let hnode107 : Eq (assignment 107) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 208 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode241)
  let hnode108 : Eq (assignment 108) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.true (h_support 183 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.true) hnode242)
  let hnode109 : Eq (assignment 109) Sign.positive :=
    Eq.trans (h_support 91 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode118 : Eq (assignment 118) Sign.positive :=
    Eq.trans (h_support 73 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode53)
  let hnode125 : Eq (assignment 125) Sign.positive :=
    Eq.trans (h_support 75 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode53)
  let hnode130 : Eq (assignment 130) Sign.positive :=
    Eq.trans (h_support 129 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode25)
  let hnode135 : Eq (assignment 135) Sign.positive :=
    Eq.trans (h_support 165 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode30)
  let hnode137 : Eq (assignment 137) Sign.negative :=
    Eq.trans (h_support 169 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode32)
  let hnode139 : Eq (assignment 139) Sign.negative :=
    Eq.trans (h_support 173 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode34)
  let hnode140 : Eq (assignment 140) Sign.positive :=
    Eq.trans (h_support 113 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode154 : Eq (assignment 154) Sign.positive :=
    Eq.trans (h_support 157 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode49)
  let hnode156 : Eq (assignment 156) Sign.positive :=
    Eq.trans (h_support 115 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode157 : Eq (assignment 157) Sign.positive :=
    Eq.trans (h_support 202 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode87)
  let hnode158 : Eq (assignment 158) Sign.negative :=
    Eq.trans (h_support 177 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode53)
  let hnode159 : Eq (assignment 159) Sign.positive :=
    Eq.trans (h_support 116 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode20)
  let hnode165 : Eq (assignment 165) Sign.negative :=
    Eq.trans (h_support 166 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode30)
  let hnode167 : Eq (assignment 167) Sign.positive :=
    Eq.trans (h_support 170 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode32)
  let hnode169 : Eq (assignment 169) Sign.positive :=
    Eq.trans (h_support 174 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode34)
  let hnode177 : Eq (assignment 177) Sign.negative :=
    Eq.trans (h_support 168 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode30)
  let hnode179 : Eq (assignment 179) Sign.negative :=
    Eq.trans (h_support 172 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode32)
  let hnode180 : Eq (assignment 180) Sign.negative :=
    Eq.trans (h_support 176 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode34)
  let hnode188 : Eq (assignment 188) Sign.negative :=
    Eq.trans (h_support 178 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode53)
  let hnode191 : Eq (assignment 191) Sign.negative :=
    Eq.trans (h_support 159 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode49)
  let hnode192 : Eq (assignment 192) Sign.negative :=
    Eq.trans (h_support 179 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode53)
  let hnode194 : Eq (assignment 194) Sign.negative :=
    Eq.trans (h_support 160 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode49)
  let hnode195 : Eq (assignment 195) Sign.negative :=
    Eq.trans (h_support 180 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode53)
  let hnode200 : Eq (assignment 200) Sign.positive :=
    Eq.trans (h_support 191 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode65)
  let hnode201 : Eq (assignment 201) Sign.negative :=
    Eq.trans (h_support 56 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode146)
  let hnode206 : Eq (assignment 206) Sign.positive :=
    Eq.trans (h_support 192 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode65)
  let hnode213 : Eq (assignment 213) Sign.positive :=
    Eq.trans (h_support 193 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode65)
  let hnode215 : Eq (assignment 215) Sign.positive :=
    Eq.trans (h_support 121 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode90)
  let hnode217 : Eq (assignment 217) Sign.positive :=
    Eq.trans (h_support 57 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode146)
  let hnode222 : Eq (assignment 222) Sign.negative :=
    Eq.trans (h_support 203 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode87)
  let hnode226 : Eq (assignment 226) Sign.negative :=
    Eq.trans (h_support 204 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode87)
  let hnode229 : Eq (assignment 229) Sign.positive :=
    Eq.trans (h_support 123 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode90)
  let hnode230 : Eq (assignment 230) Sign.positive :=
    Eq.trans (h_support 205 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode87)
  let hnode18 : Eq (assignment 18) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 107 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode154)
  let hnode33 : Eq (assignment 33) Sign.negative :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 155 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode177)
  let hnode68 : Eq (assignment 68) Sign.positive :=
    Eq.trans (Sign.reverse_support Bool.false (h_support 201 (of_decide_eq_true (Eq.refl Bool.true)))) (congrArg (Sign.withNegation Bool.false) hnode215)
  let hnode69 : Eq (assignment 69) Sign.positive :=
    Eq.trans (h_support 68 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode19)
  let hnode136 : Eq (assignment 136) Sign.negative :=
    Eq.trans (h_support 194 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode66)
  let hnode149 : Eq (assignment 149) Sign.negative :=
    Eq.trans (h_support 110 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode19)
  let hnode155 : Eq (assignment 155) Sign.negative :=
    Eq.trans (h_support 111 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode19)
  let hnode209 : Eq (assignment 209) Sign.positive :=
    Eq.trans (h_support 161 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode104)
  let hnode214 : Eq (assignment 214) Sign.negative :=
    Eq.trans (h_support 197 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode66)
  let hnode223 : Eq (assignment 223) Sign.positive :=
    Eq.trans (h_support 77 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode158)
  let hnode227 : Eq (assignment 227) Sign.positive :=
    Eq.trans (h_support 78 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode158)
  let hnode234 : Eq (assignment 234) Sign.negative :=
    Eq.trans (h_support 162 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode104)
  let hnode237 : Eq (assignment 237) Sign.positive :=
    Eq.trans (h_support 207 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode107)
  let hnode238 : Eq (assignment 238) Sign.negative :=
    Eq.trans (h_support 182 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode108)
  let hnode244 : Eq (assignment 244) Sign.positive :=
    Eq.trans (h_support 164 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode104)
  let hnode245 : Eq (assignment 245) Sign.negative :=
    Eq.trans (h_support 184 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode108)
  let hnode138 : Eq (assignment 138) Sign.positive :=
    Eq.trans (h_support 153 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.true) hnode33)
  let hnode148 : Eq (assignment 148) Sign.positive :=
    Eq.trans (h_support 106 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode18)
  let hnode168 : Eq (assignment 168) Sign.negative :=
    Eq.trans (h_support 154 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode33)
  let hnode203 : Eq (assignment 203) Sign.positive :=
    Eq.trans (h_support 199 (of_decide_eq_true (Eq.refl Bool.true))) (congrArg (Sign.withNegation Bool.false) hnode68)
  let predicate : Nat → Prop := fun index =>
    Eq ((Cases.C021.initial index).allows
      (Sign.withNegation globalNegation (assignment index))) Bool.true
  let bounded0 := below_zero predicate
  let bounded1 := below_succ bounded0 (top_allows (Sign.withNegation globalNegation (assignment 0)))
  let bounded2 := below_succ bounded1 (top_allows (Sign.withNegation globalNegation (assignment 1)))
  let bounded3 := below_succ bounded2 (top_allows (Sign.withNegation globalNegation (assignment 2)))
  let bounded4 := below_succ bounded3 (top_allows (Sign.withNegation globalNegation (assignment 3)))
  let bounded5 := below_succ bounded4 (top_allows (Sign.withNegation globalNegation (assignment 4)))
  let bounded6 := below_succ bounded5 (top_allows (Sign.withNegation globalNegation (assignment 5)))
  let bounded7 := below_succ bounded6 (domain_from_eq (domain := Cases.C021.initial 6) (congrArg (Sign.withNegation globalNegation) h_anchor) (Eq.refl Bool.true))
  let bounded8 := below_succ bounded7 (domain_from_eq (domain := Cases.C021.initial 7) (congrArg (Sign.withNegation globalNegation) hnode7) (Eq.refl Bool.true))
  let bounded9 := below_succ bounded8 (top_allows (Sign.withNegation globalNegation (assignment 8)))
  let bounded10 := below_succ bounded9 (domain_from_eq (domain := Cases.C021.initial 9) (congrArg (Sign.withNegation globalNegation) hnode9) (Eq.refl Bool.true))
  let bounded11 := below_succ bounded10 (domain_from_eq (domain := Cases.C021.initial 10) (congrArg (Sign.withNegation globalNegation) hnode10) (Eq.refl Bool.true))
  let bounded12 := below_succ bounded11 (top_allows (Sign.withNegation globalNegation (assignment 11)))
  let bounded13 := below_succ bounded12 (top_allows (Sign.withNegation globalNegation (assignment 12)))
  let bounded14 := below_succ bounded13 (domain_from_eq (domain := Cases.C021.initial 13) (congrArg (Sign.withNegation globalNegation) hnode13) (Eq.refl Bool.true))
  let bounded15 := below_succ bounded14 (domain_from_eq (domain := Cases.C021.initial 14) (congrArg (Sign.withNegation globalNegation) hnode14) (Eq.refl Bool.true))
  let bounded16 := below_succ bounded15 (domain_from_eq (domain := Cases.C021.initial 15) (congrArg (Sign.withNegation globalNegation) hnode15) (Eq.refl Bool.true))
  let bounded17 := below_succ bounded16 (domain_from_eq (domain := Cases.C021.initial 16) (congrArg (Sign.withNegation globalNegation) hnode16) (Eq.refl Bool.true))
  let bounded18 := below_succ bounded17 (domain_from_eq (domain := Cases.C021.initial 17) (congrArg (Sign.withNegation globalNegation) hnode17) (Eq.refl Bool.true))
  let bounded19 := below_succ bounded18 (domain_from_eq (domain := Cases.C021.initial 18) (congrArg (Sign.withNegation globalNegation) hnode18) (Eq.refl Bool.true))
  let bounded20 := below_succ bounded19 (domain_from_eq (domain := Cases.C021.initial 19) (congrArg (Sign.withNegation globalNegation) hnode19) (Eq.refl Bool.true))
  let bounded21 := below_succ bounded20 (domain_from_eq (domain := Cases.C021.initial 20) (congrArg (Sign.withNegation globalNegation) hnode20) (Eq.refl Bool.true))
  let bounded22 := below_succ bounded21 (domain_from_eq (domain := Cases.C021.initial 21) (congrArg (Sign.withNegation globalNegation) hnode21) (Eq.refl Bool.true))
  let bounded23 := below_succ bounded22 (top_allows (Sign.withNegation globalNegation (assignment 22)))
  let bounded24 := below_succ bounded23 (top_allows (Sign.withNegation globalNegation (assignment 23)))
  let bounded25 := below_succ bounded24 (domain_from_eq (domain := Cases.C021.initial 24) (congrArg (Sign.withNegation globalNegation) hnode24) (Eq.refl Bool.true))
  let bounded26 := below_succ bounded25 (domain_from_eq (domain := Cases.C021.initial 25) (congrArg (Sign.withNegation globalNegation) hnode25) (Eq.refl Bool.true))
  let bounded27 := below_succ bounded26 (domain_from_eq (domain := Cases.C021.initial 26) (congrArg (Sign.withNegation globalNegation) hnode26) (Eq.refl Bool.true))
  let bounded28 := below_succ bounded27 (domain_from_eq (domain := Cases.C021.initial 27) (congrArg (Sign.withNegation globalNegation) hnode27) (Eq.refl Bool.true))
  let bounded29 := below_succ bounded28 (domain_from_eq (domain := Cases.C021.initial 28) (congrArg (Sign.withNegation globalNegation) hnode28) (Eq.refl Bool.true))
  let bounded30 := below_succ bounded29 (domain_from_eq (domain := Cases.C021.initial 29) (congrArg (Sign.withNegation globalNegation) hnode29) (Eq.refl Bool.true))
  let bounded31 := below_succ bounded30 (domain_from_eq (domain := Cases.C021.initial 30) (congrArg (Sign.withNegation globalNegation) hnode30) (Eq.refl Bool.true))
  let bounded32 := below_succ bounded31 (top_allows (Sign.withNegation globalNegation (assignment 31)))
  let bounded33 := below_succ bounded32 (domain_from_eq (domain := Cases.C021.initial 32) (congrArg (Sign.withNegation globalNegation) hnode32) (Eq.refl Bool.true))
  let bounded34 := below_succ bounded33 (domain_from_eq (domain := Cases.C021.initial 33) (congrArg (Sign.withNegation globalNegation) hnode33) (Eq.refl Bool.true))
  let bounded35 := below_succ bounded34 (domain_from_eq (domain := Cases.C021.initial 34) (congrArg (Sign.withNegation globalNegation) hnode34) (Eq.refl Bool.true))
  let bounded36 := below_succ bounded35 (top_allows (Sign.withNegation globalNegation (assignment 35)))
  let bounded37 := below_succ bounded36 (domain_from_eq (domain := Cases.C021.initial 36) (congrArg (Sign.withNegation globalNegation) hnode36) (Eq.refl Bool.true))
  let bounded38 := below_succ bounded37 (domain_from_eq (domain := Cases.C021.initial 37) (congrArg (Sign.withNegation globalNegation) hnode37) (Eq.refl Bool.true))
  let bounded39 := below_succ bounded38 (domain_from_eq (domain := Cases.C021.initial 38) (congrArg (Sign.withNegation globalNegation) (h_zero 0 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded40 := below_succ bounded39 (domain_from_eq (domain := Cases.C021.initial 39) (congrArg (Sign.withNegation globalNegation) hnode39) (Eq.refl Bool.true))
  let bounded41 := below_succ bounded40 (top_allows (Sign.withNegation globalNegation (assignment 40)))
  let bounded42 := below_succ bounded41 (domain_from_eq (domain := Cases.C021.initial 41) (congrArg (Sign.withNegation globalNegation) hnode41) (Eq.refl Bool.true))
  let bounded43 := below_succ bounded42 (top_allows (Sign.withNegation globalNegation (assignment 42)))
  let bounded44 := below_succ bounded43 (domain_from_eq (domain := Cases.C021.initial 43) (congrArg (Sign.withNegation globalNegation) hnode43) (Eq.refl Bool.true))
  let bounded45 := below_succ bounded44 (top_allows (Sign.withNegation globalNegation (assignment 44)))
  let bounded46 := below_succ bounded45 (domain_from_eq (domain := Cases.C021.initial 45) (congrArg (Sign.withNegation globalNegation) hnode45) (Eq.refl Bool.true))
  let bounded47 := below_succ bounded46 (top_allows (Sign.withNegation globalNegation (assignment 46)))
  let bounded48 := below_succ bounded47 (domain_from_eq (domain := Cases.C021.initial 47) (congrArg (Sign.withNegation globalNegation) hnode47) (Eq.refl Bool.true))
  let bounded49 := below_succ bounded48 (domain_from_eq (domain := Cases.C021.initial 48) (congrArg (Sign.withNegation globalNegation) hnode48) (Eq.refl Bool.true))
  let bounded50 := below_succ bounded49 (domain_from_eq (domain := Cases.C021.initial 49) (congrArg (Sign.withNegation globalNegation) hnode49) (Eq.refl Bool.true))
  let bounded51 := below_succ bounded50 (top_allows (Sign.withNegation globalNegation (assignment 50)))
  let bounded52 := below_succ bounded51 (domain_from_eq (domain := Cases.C021.initial 51) (congrArg (Sign.withNegation globalNegation) hnode51) (Eq.refl Bool.true))
  let bounded53 := below_succ bounded52 (top_allows (Sign.withNegation globalNegation (assignment 52)))
  let bounded54 := below_succ bounded53 (domain_from_eq (domain := Cases.C021.initial 53) (congrArg (Sign.withNegation globalNegation) hnode53) (Eq.refl Bool.true))
  let bounded55 := below_succ bounded54 (top_allows (Sign.withNegation globalNegation (assignment 54)))
  let bounded56 := below_succ bounded55 (domain_from_eq (domain := Cases.C021.initial 55) (congrArg (Sign.withNegation globalNegation) hnode55) (Eq.refl Bool.true))
  let bounded57 := below_succ bounded56 (domain_from_eq (domain := Cases.C021.initial 56) (congrArg (Sign.withNegation globalNegation) hnode56) (Eq.refl Bool.true))
  let bounded58 := below_succ bounded57 (domain_from_eq (domain := Cases.C021.initial 57) (congrArg (Sign.withNegation globalNegation) hnode57) (Eq.refl Bool.true))
  let bounded59 := below_succ bounded58 (top_allows (Sign.withNegation globalNegation (assignment 58)))
  let bounded60 := below_succ bounded59 (domain_from_eq (domain := Cases.C021.initial 59) (congrArg (Sign.withNegation globalNegation) hnode59) (Eq.refl Bool.true))
  let bounded61 := below_succ bounded60 (domain_from_eq (domain := Cases.C021.initial 60) (congrArg (Sign.withNegation globalNegation) hnode60) (Eq.refl Bool.true))
  let bounded62 := below_succ bounded61 (domain_from_eq (domain := Cases.C021.initial 61) (congrArg (Sign.withNegation globalNegation) hnode61) (Eq.refl Bool.true))
  let bounded63 := below_succ bounded62 (top_allows (Sign.withNegation globalNegation (assignment 62)))
  let bounded64 := below_succ bounded63 (top_allows (Sign.withNegation globalNegation (assignment 63)))
  let bounded65 := below_succ bounded64 (domain_from_eq (domain := Cases.C021.initial 64) (congrArg (Sign.withNegation globalNegation) hnode64) (Eq.refl Bool.true))
  let bounded66 := below_succ bounded65 (domain_from_eq (domain := Cases.C021.initial 65) (congrArg (Sign.withNegation globalNegation) hnode65) (Eq.refl Bool.true))
  let bounded67 := below_succ bounded66 (domain_from_eq (domain := Cases.C021.initial 66) (congrArg (Sign.withNegation globalNegation) hnode66) (Eq.refl Bool.true))
  let bounded68 := below_succ bounded67 (domain_from_eq (domain := Cases.C021.initial 67) (congrArg (Sign.withNegation globalNegation) hnode67) (Eq.refl Bool.true))
  let bounded69 := below_succ bounded68 (domain_from_eq (domain := Cases.C021.initial 68) (congrArg (Sign.withNegation globalNegation) hnode68) (Eq.refl Bool.true))
  let bounded70 := below_succ bounded69 (domain_from_eq (domain := Cases.C021.initial 69) (congrArg (Sign.withNegation globalNegation) hnode69) (Eq.refl Bool.true))
  let bounded71 := below_succ bounded70 (top_allows (Sign.withNegation globalNegation (assignment 70)))
  let bounded72 := below_succ bounded71 (domain_from_eq (domain := Cases.C021.initial 71) (congrArg (Sign.withNegation globalNegation) hnode71) (Eq.refl Bool.true))
  let bounded73 := below_succ bounded72 (domain_from_eq (domain := Cases.C021.initial 72) (congrArg (Sign.withNegation globalNegation) hnode72) (Eq.refl Bool.true))
  let bounded74 := below_succ bounded73 (domain_from_eq (domain := Cases.C021.initial 73) (congrArg (Sign.withNegation globalNegation) hnode73) (Eq.refl Bool.true))
  let bounded75 := below_succ bounded74 (domain_from_eq (domain := Cases.C021.initial 74) (congrArg (Sign.withNegation globalNegation) (h_zero 1 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded76 := below_succ bounded75 (domain_from_eq (domain := Cases.C021.initial 75) (congrArg (Sign.withNegation globalNegation) hnode75) (Eq.refl Bool.true))
  let bounded77 := below_succ bounded76 (domain_from_eq (domain := Cases.C021.initial 76) (congrArg (Sign.withNegation globalNegation) (h_zero 2 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded78 := below_succ bounded77 (domain_from_eq (domain := Cases.C021.initial 77) (congrArg (Sign.withNegation globalNegation) hnode77) (Eq.refl Bool.true))
  let bounded79 := below_succ bounded78 (domain_from_eq (domain := Cases.C021.initial 78) (congrArg (Sign.withNegation globalNegation) hnode78) (Eq.refl Bool.true))
  let bounded80 := below_succ bounded79 (domain_from_eq (domain := Cases.C021.initial 79) (congrArg (Sign.withNegation globalNegation) hnode79) (Eq.refl Bool.true))
  let bounded81 := below_succ bounded80 (domain_from_eq (domain := Cases.C021.initial 80) (congrArg (Sign.withNegation globalNegation) hnode80) (Eq.refl Bool.true))
  let bounded82 := below_succ bounded81 (domain_from_eq (domain := Cases.C021.initial 81) (congrArg (Sign.withNegation globalNegation) hnode81) (Eq.refl Bool.true))
  let bounded83 := below_succ bounded82 (domain_from_eq (domain := Cases.C021.initial 82) (congrArg (Sign.withNegation globalNegation) hnode82) (Eq.refl Bool.true))
  let bounded84 := below_succ bounded83 (domain_from_eq (domain := Cases.C021.initial 83) (congrArg (Sign.withNegation globalNegation) hnode83) (Eq.refl Bool.true))
  let bounded85 := below_succ bounded84 (top_allows (Sign.withNegation globalNegation (assignment 84)))
  let bounded86 := below_succ bounded85 (domain_from_eq (domain := Cases.C021.initial 85) (congrArg (Sign.withNegation globalNegation) hnode85) (Eq.refl Bool.true))
  let bounded87 := below_succ bounded86 (domain_from_eq (domain := Cases.C021.initial 86) (congrArg (Sign.withNegation globalNegation) hnode86) (Eq.refl Bool.true))
  let bounded88 := below_succ bounded87 (domain_from_eq (domain := Cases.C021.initial 87) (congrArg (Sign.withNegation globalNegation) hnode87) (Eq.refl Bool.true))
  let bounded89 := below_succ bounded88 (domain_from_eq (domain := Cases.C021.initial 88) (congrArg (Sign.withNegation globalNegation) (h_zero 3 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded90 := below_succ bounded89 (domain_from_eq (domain := Cases.C021.initial 89) (congrArg (Sign.withNegation globalNegation) hnode89) (Eq.refl Bool.true))
  let bounded91 := below_succ bounded90 (domain_from_eq (domain := Cases.C021.initial 90) (congrArg (Sign.withNegation globalNegation) hnode90) (Eq.refl Bool.true))
  let bounded92 := below_succ bounded91 (domain_from_eq (domain := Cases.C021.initial 91) (congrArg (Sign.withNegation globalNegation) hnode91) (Eq.refl Bool.true))
  let bounded93 := below_succ bounded92 (top_allows (Sign.withNegation globalNegation (assignment 92)))
  let bounded94 := below_succ bounded93 (domain_from_eq (domain := Cases.C021.initial 93) (congrArg (Sign.withNegation globalNegation) hnode93) (Eq.refl Bool.true))
  let bounded95 := below_succ bounded94 (domain_from_eq (domain := Cases.C021.initial 94) (congrArg (Sign.withNegation globalNegation) hnode94) (Eq.refl Bool.true))
  let bounded96 := below_succ bounded95 (top_allows (Sign.withNegation globalNegation (assignment 95)))
  let bounded97 := below_succ bounded96 (domain_from_eq (domain := Cases.C021.initial 96) (congrArg (Sign.withNegation globalNegation) hnode96) (Eq.refl Bool.true))
  let bounded98 := below_succ bounded97 (domain_from_eq (domain := Cases.C021.initial 97) (congrArg (Sign.withNegation globalNegation) hnode97) (Eq.refl Bool.true))
  let bounded99 := below_succ bounded98 (top_allows (Sign.withNegation globalNegation (assignment 98)))
  let bounded100 := below_succ bounded99 (top_allows (Sign.withNegation globalNegation (assignment 99)))
  let bounded101 := below_succ bounded100 (top_allows (Sign.withNegation globalNegation (assignment 100)))
  let bounded102 := below_succ bounded101 (domain_from_eq (domain := Cases.C021.initial 101) (congrArg (Sign.withNegation globalNegation) hnode101) (Eq.refl Bool.true))
  let bounded103 := below_succ bounded102 (domain_from_eq (domain := Cases.C021.initial 102) (congrArg (Sign.withNegation globalNegation) hnode102) (Eq.refl Bool.true))
  let bounded104 := below_succ bounded103 (domain_from_eq (domain := Cases.C021.initial 103) (congrArg (Sign.withNegation globalNegation) (h_zero 4 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded105 := below_succ bounded104 (domain_from_eq (domain := Cases.C021.initial 104) (congrArg (Sign.withNegation globalNegation) hnode104) (Eq.refl Bool.true))
  let bounded106 := below_succ bounded105 (domain_from_eq (domain := Cases.C021.initial 105) (congrArg (Sign.withNegation globalNegation) hnode105) (Eq.refl Bool.true))
  let bounded107 := below_succ bounded106 (domain_from_eq (domain := Cases.C021.initial 106) (congrArg (Sign.withNegation globalNegation) hnode106) (Eq.refl Bool.true))
  let bounded108 := below_succ bounded107 (domain_from_eq (domain := Cases.C021.initial 107) (congrArg (Sign.withNegation globalNegation) hnode107) (Eq.refl Bool.true))
  let bounded109 := below_succ bounded108 (domain_from_eq (domain := Cases.C021.initial 108) (congrArg (Sign.withNegation globalNegation) hnode108) (Eq.refl Bool.true))
  let bounded110 := below_succ bounded109 (domain_from_eq (domain := Cases.C021.initial 109) (congrArg (Sign.withNegation globalNegation) hnode109) (Eq.refl Bool.true))
  let bounded111 := below_succ bounded110 (top_allows (Sign.withNegation globalNegation (assignment 110)))
  let bounded112 := below_succ bounded111 (top_allows (Sign.withNegation globalNegation (assignment 111)))
  let bounded113 := below_succ bounded112 (domain_from_eq (domain := Cases.C021.initial 112) (congrArg (Sign.withNegation globalNegation) hnode112) (Eq.refl Bool.true))
  let bounded114 := below_succ bounded113 (domain_from_eq (domain := Cases.C021.initial 113) (congrArg (Sign.withNegation globalNegation) hnode113) (Eq.refl Bool.true))
  let bounded115 := below_succ bounded114 (domain_from_eq (domain := Cases.C021.initial 114) (congrArg (Sign.withNegation globalNegation) hnode114) (Eq.refl Bool.true))
  let bounded116 := below_succ bounded115 (domain_from_eq (domain := Cases.C021.initial 115) (congrArg (Sign.withNegation globalNegation) hnode115) (Eq.refl Bool.true))
  let bounded117 := below_succ bounded116 (domain_from_eq (domain := Cases.C021.initial 116) (congrArg (Sign.withNegation globalNegation) hnode116) (Eq.refl Bool.true))
  let bounded118 := below_succ bounded117 (domain_from_eq (domain := Cases.C021.initial 117) (congrArg (Sign.withNegation globalNegation) hnode117) (Eq.refl Bool.true))
  let bounded119 := below_succ bounded118 (domain_from_eq (domain := Cases.C021.initial 118) (congrArg (Sign.withNegation globalNegation) hnode118) (Eq.refl Bool.true))
  let bounded120 := below_succ bounded119 (domain_from_eq (domain := Cases.C021.initial 119) (congrArg (Sign.withNegation globalNegation) hnode119) (Eq.refl Bool.true))
  let bounded121 := below_succ bounded120 (top_allows (Sign.withNegation globalNegation (assignment 120)))
  let bounded122 := below_succ bounded121 (domain_from_eq (domain := Cases.C021.initial 121) (congrArg (Sign.withNegation globalNegation) hnode121) (Eq.refl Bool.true))
  let bounded123 := below_succ bounded122 (domain_from_eq (domain := Cases.C021.initial 122) (congrArg (Sign.withNegation globalNegation) hnode122) (Eq.refl Bool.true))
  let bounded124 := below_succ bounded123 (domain_from_eq (domain := Cases.C021.initial 123) (congrArg (Sign.withNegation globalNegation) hnode123) (Eq.refl Bool.true))
  let bounded125 := below_succ bounded124 (top_allows (Sign.withNegation globalNegation (assignment 124)))
  let bounded126 := below_succ bounded125 (domain_from_eq (domain := Cases.C021.initial 125) (congrArg (Sign.withNegation globalNegation) hnode125) (Eq.refl Bool.true))
  let bounded127 := below_succ bounded126 (domain_from_eq (domain := Cases.C021.initial 126) (congrArg (Sign.withNegation globalNegation) hnode126) (Eq.refl Bool.true))
  let bounded128 := below_succ bounded127 (top_allows (Sign.withNegation globalNegation (assignment 127)))
  let bounded129 := below_succ bounded128 (top_allows (Sign.withNegation globalNegation (assignment 128)))
  let bounded130 := below_succ bounded129 (top_allows (Sign.withNegation globalNegation (assignment 129)))
  let bounded131 := below_succ bounded130 (domain_from_eq (domain := Cases.C021.initial 130) (congrArg (Sign.withNegation globalNegation) hnode130) (Eq.refl Bool.true))
  let bounded132 := below_succ bounded131 (top_allows (Sign.withNegation globalNegation (assignment 131)))
  let bounded133 := below_succ bounded132 (domain_from_eq (domain := Cases.C021.initial 132) (congrArg (Sign.withNegation globalNegation) hnode132) (Eq.refl Bool.true))
  let bounded134 := below_succ bounded133 (domain_from_eq (domain := Cases.C021.initial 133) (congrArg (Sign.withNegation globalNegation) hnode133) (Eq.refl Bool.true))
  let bounded135 := below_succ bounded134 (domain_from_eq (domain := Cases.C021.initial 134) (congrArg (Sign.withNegation globalNegation) hnode134) (Eq.refl Bool.true))
  let bounded136 := below_succ bounded135 (domain_from_eq (domain := Cases.C021.initial 135) (congrArg (Sign.withNegation globalNegation) hnode135) (Eq.refl Bool.true))
  let bounded137 := below_succ bounded136 (domain_from_eq (domain := Cases.C021.initial 136) (congrArg (Sign.withNegation globalNegation) hnode136) (Eq.refl Bool.true))
  let bounded138 := below_succ bounded137 (domain_from_eq (domain := Cases.C021.initial 137) (congrArg (Sign.withNegation globalNegation) hnode137) (Eq.refl Bool.true))
  let bounded139 := below_succ bounded138 (domain_from_eq (domain := Cases.C021.initial 138) (congrArg (Sign.withNegation globalNegation) hnode138) (Eq.refl Bool.true))
  let bounded140 := below_succ bounded139 (domain_from_eq (domain := Cases.C021.initial 139) (congrArg (Sign.withNegation globalNegation) hnode139) (Eq.refl Bool.true))
  let bounded141 := below_succ bounded140 (domain_from_eq (domain := Cases.C021.initial 140) (congrArg (Sign.withNegation globalNegation) hnode140) (Eq.refl Bool.true))
  let bounded142 := below_succ bounded141 (top_allows (Sign.withNegation globalNegation (assignment 141)))
  let bounded143 := below_succ bounded142 (top_allows (Sign.withNegation globalNegation (assignment 142)))
  let bounded144 := below_succ bounded143 (domain_from_eq (domain := Cases.C021.initial 143) (congrArg (Sign.withNegation globalNegation) hnode143) (Eq.refl Bool.true))
  let bounded145 := below_succ bounded144 (domain_from_eq (domain := Cases.C021.initial 144) (congrArg (Sign.withNegation globalNegation) hnode144) (Eq.refl Bool.true))
  let bounded146 := below_succ bounded145 (top_allows (Sign.withNegation globalNegation (assignment 145)))
  let bounded147 := below_succ bounded146 (domain_from_eq (domain := Cases.C021.initial 146) (congrArg (Sign.withNegation globalNegation) hnode146) (Eq.refl Bool.true))
  let bounded148 := below_succ bounded147 (top_allows (Sign.withNegation globalNegation (assignment 147)))
  let bounded149 := below_succ bounded148 (domain_from_eq (domain := Cases.C021.initial 148) (congrArg (Sign.withNegation globalNegation) hnode148) (Eq.refl Bool.true))
  let bounded150 := below_succ bounded149 (domain_from_eq (domain := Cases.C021.initial 149) (congrArg (Sign.withNegation globalNegation) hnode149) (Eq.refl Bool.true))
  let bounded151 := below_succ bounded150 (domain_from_eq (domain := Cases.C021.initial 150) (congrArg (Sign.withNegation globalNegation) hnode150) (Eq.refl Bool.true))
  let bounded152 := below_succ bounded151 (top_allows (Sign.withNegation globalNegation (assignment 151)))
  let bounded153 := below_succ bounded152 (top_allows (Sign.withNegation globalNegation (assignment 152)))
  let bounded154 := below_succ bounded153 (top_allows (Sign.withNegation globalNegation (assignment 153)))
  let bounded155 := below_succ bounded154 (domain_from_eq (domain := Cases.C021.initial 154) (congrArg (Sign.withNegation globalNegation) hnode154) (Eq.refl Bool.true))
  let bounded156 := below_succ bounded155 (domain_from_eq (domain := Cases.C021.initial 155) (congrArg (Sign.withNegation globalNegation) hnode155) (Eq.refl Bool.true))
  let bounded157 := below_succ bounded156 (domain_from_eq (domain := Cases.C021.initial 156) (congrArg (Sign.withNegation globalNegation) hnode156) (Eq.refl Bool.true))
  let bounded158 := below_succ bounded157 (domain_from_eq (domain := Cases.C021.initial 157) (congrArg (Sign.withNegation globalNegation) hnode157) (Eq.refl Bool.true))
  let bounded159 := below_succ bounded158 (domain_from_eq (domain := Cases.C021.initial 158) (congrArg (Sign.withNegation globalNegation) hnode158) (Eq.refl Bool.true))
  let bounded160 := below_succ bounded159 (domain_from_eq (domain := Cases.C021.initial 159) (congrArg (Sign.withNegation globalNegation) hnode159) (Eq.refl Bool.true))
  let bounded161 := below_succ bounded160 (domain_from_eq (domain := Cases.C021.initial 160) (congrArg (Sign.withNegation globalNegation) (h_zero 5 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded162 := below_succ bounded161 (domain_from_eq (domain := Cases.C021.initial 161) (congrArg (Sign.withNegation globalNegation) hnode161) (Eq.refl Bool.true))
  let bounded163 := below_succ bounded162 (domain_from_eq (domain := Cases.C021.initial 162) (congrArg (Sign.withNegation globalNegation) hnode162) (Eq.refl Bool.true))
  let bounded164 := below_succ bounded163 (domain_from_eq (domain := Cases.C021.initial 163) (congrArg (Sign.withNegation globalNegation) hnode163) (Eq.refl Bool.true))
  let bounded165 := below_succ bounded164 (domain_from_eq (domain := Cases.C021.initial 164) (congrArg (Sign.withNegation globalNegation) (h_zero 6 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded166 := below_succ bounded165 (domain_from_eq (domain := Cases.C021.initial 165) (congrArg (Sign.withNegation globalNegation) hnode165) (Eq.refl Bool.true))
  let bounded167 := below_succ bounded166 (top_allows (Sign.withNegation globalNegation (assignment 166)))
  let bounded168 := below_succ bounded167 (domain_from_eq (domain := Cases.C021.initial 167) (congrArg (Sign.withNegation globalNegation) hnode167) (Eq.refl Bool.true))
  let bounded169 := below_succ bounded168 (domain_from_eq (domain := Cases.C021.initial 168) (congrArg (Sign.withNegation globalNegation) hnode168) (Eq.refl Bool.true))
  let bounded170 := below_succ bounded169 (domain_from_eq (domain := Cases.C021.initial 169) (congrArg (Sign.withNegation globalNegation) hnode169) (Eq.refl Bool.true))
  let bounded171 := below_succ bounded170 (domain_from_eq (domain := Cases.C021.initial 170) (congrArg (Sign.withNegation globalNegation) hnode170) (Eq.refl Bool.true))
  let bounded172 := below_succ bounded171 (domain_from_eq (domain := Cases.C021.initial 171) (congrArg (Sign.withNegation globalNegation) hnode171) (Eq.refl Bool.true))
  let bounded173 := below_succ bounded172 (domain_from_eq (domain := Cases.C021.initial 172) (congrArg (Sign.withNegation globalNegation) hnode172) (Eq.refl Bool.true))
  let bounded174 := below_succ bounded173 (domain_from_eq (domain := Cases.C021.initial 173) (congrArg (Sign.withNegation globalNegation) hnode173) (Eq.refl Bool.true))
  let bounded175 := below_succ bounded174 (domain_from_eq (domain := Cases.C021.initial 174) (congrArg (Sign.withNegation globalNegation) (h_zero 7 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded176 := below_succ bounded175 (domain_from_eq (domain := Cases.C021.initial 175) (congrArg (Sign.withNegation globalNegation) hnode175) (Eq.refl Bool.true))
  let bounded177 := below_succ bounded176 (domain_from_eq (domain := Cases.C021.initial 176) (congrArg (Sign.withNegation globalNegation) hnode176) (Eq.refl Bool.true))
  let bounded178 := below_succ bounded177 (domain_from_eq (domain := Cases.C021.initial 177) (congrArg (Sign.withNegation globalNegation) hnode177) (Eq.refl Bool.true))
  let bounded179 := below_succ bounded178 (domain_from_eq (domain := Cases.C021.initial 178) (congrArg (Sign.withNegation globalNegation) (h_zero 8 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded180 := below_succ bounded179 (domain_from_eq (domain := Cases.C021.initial 179) (congrArg (Sign.withNegation globalNegation) hnode179) (Eq.refl Bool.true))
  let bounded181 := below_succ bounded180 (domain_from_eq (domain := Cases.C021.initial 180) (congrArg (Sign.withNegation globalNegation) hnode180) (Eq.refl Bool.true))
  let bounded182 := below_succ bounded181 (top_allows (Sign.withNegation globalNegation (assignment 181)))
  let bounded183 := below_succ bounded182 (domain_from_eq (domain := Cases.C021.initial 182) (congrArg (Sign.withNegation globalNegation) hnode182) (Eq.refl Bool.true))
  let bounded184 := below_succ bounded183 (domain_from_eq (domain := Cases.C021.initial 183) (congrArg (Sign.withNegation globalNegation) hnode183) (Eq.refl Bool.true))
  let bounded185 := below_succ bounded184 (domain_from_eq (domain := Cases.C021.initial 184) (congrArg (Sign.withNegation globalNegation) hnode184) (Eq.refl Bool.true))
  let bounded186 := below_succ bounded185 (domain_from_eq (domain := Cases.C021.initial 185) (congrArg (Sign.withNegation globalNegation) hnode185) (Eq.refl Bool.true))
  let bounded187 := below_succ bounded186 (domain_from_eq (domain := Cases.C021.initial 186) (congrArg (Sign.withNegation globalNegation) hnode186) (Eq.refl Bool.true))
  let bounded188 := below_succ bounded187 (top_allows (Sign.withNegation globalNegation (assignment 187)))
  let bounded189 := below_succ bounded188 (domain_from_eq (domain := Cases.C021.initial 188) (congrArg (Sign.withNegation globalNegation) hnode188) (Eq.refl Bool.true))
  let bounded190 := below_succ bounded189 (domain_from_eq (domain := Cases.C021.initial 189) (congrArg (Sign.withNegation globalNegation) hnode189) (Eq.refl Bool.true))
  let bounded191 := below_succ bounded190 (domain_from_eq (domain := Cases.C021.initial 190) (congrArg (Sign.withNegation globalNegation) hnode190) (Eq.refl Bool.true))
  let bounded192 := below_succ bounded191 (domain_from_eq (domain := Cases.C021.initial 191) (congrArg (Sign.withNegation globalNegation) hnode191) (Eq.refl Bool.true))
  let bounded193 := below_succ bounded192 (domain_from_eq (domain := Cases.C021.initial 192) (congrArg (Sign.withNegation globalNegation) hnode192) (Eq.refl Bool.true))
  let bounded194 := below_succ bounded193 (top_allows (Sign.withNegation globalNegation (assignment 193)))
  let bounded195 := below_succ bounded194 (domain_from_eq (domain := Cases.C021.initial 194) (congrArg (Sign.withNegation globalNegation) hnode194) (Eq.refl Bool.true))
  let bounded196 := below_succ bounded195 (domain_from_eq (domain := Cases.C021.initial 195) (congrArg (Sign.withNegation globalNegation) hnode195) (Eq.refl Bool.true))
  let bounded197 := below_succ bounded196 (top_allows (Sign.withNegation globalNegation (assignment 196)))
  let bounded198 := below_succ bounded197 (top_allows (Sign.withNegation globalNegation (assignment 197)))
  let bounded199 := below_succ bounded198 (top_allows (Sign.withNegation globalNegation (assignment 198)))
  let bounded200 := below_succ bounded199 (domain_from_eq (domain := Cases.C021.initial 199) (congrArg (Sign.withNegation globalNegation) hnode199) (Eq.refl Bool.true))
  let bounded201 := below_succ bounded200 (domain_from_eq (domain := Cases.C021.initial 200) (congrArg (Sign.withNegation globalNegation) hnode200) (Eq.refl Bool.true))
  let bounded202 := below_succ bounded201 (domain_from_eq (domain := Cases.C021.initial 201) (congrArg (Sign.withNegation globalNegation) hnode201) (Eq.refl Bool.true))
  let bounded203 := below_succ bounded202 (top_allows (Sign.withNegation globalNegation (assignment 202)))
  let bounded204 := below_succ bounded203 (domain_from_eq (domain := Cases.C021.initial 203) (congrArg (Sign.withNegation globalNegation) hnode203) (Eq.refl Bool.true))
  let bounded205 := below_succ bounded204 (top_allows (Sign.withNegation globalNegation (assignment 204)))
  let bounded206 := below_succ bounded205 (domain_from_eq (domain := Cases.C021.initial 205) (congrArg (Sign.withNegation globalNegation) hnode205) (Eq.refl Bool.true))
  let bounded207 := below_succ bounded206 (domain_from_eq (domain := Cases.C021.initial 206) (congrArg (Sign.withNegation globalNegation) hnode206) (Eq.refl Bool.true))
  let bounded208 := below_succ bounded207 (domain_from_eq (domain := Cases.C021.initial 207) (congrArg (Sign.withNegation globalNegation) hnode207) (Eq.refl Bool.true))
  let bounded209 := below_succ bounded208 (domain_from_eq (domain := Cases.C021.initial 208) (congrArg (Sign.withNegation globalNegation) hnode208) (Eq.refl Bool.true))
  let bounded210 := below_succ bounded209 (domain_from_eq (domain := Cases.C021.initial 209) (congrArg (Sign.withNegation globalNegation) hnode209) (Eq.refl Bool.true))
  let bounded211 := below_succ bounded210 (top_allows (Sign.withNegation globalNegation (assignment 210)))
  let bounded212 := below_succ bounded211 (top_allows (Sign.withNegation globalNegation (assignment 211)))
  let bounded213 := below_succ bounded212 (domain_from_eq (domain := Cases.C021.initial 212) (congrArg (Sign.withNegation globalNegation) (h_zero 9 (of_decide_eq_true (Eq.refl Bool.true)))) (Eq.refl Bool.true))
  let bounded214 := below_succ bounded213 (domain_from_eq (domain := Cases.C021.initial 213) (congrArg (Sign.withNegation globalNegation) hnode213) (Eq.refl Bool.true))
  let bounded215 := below_succ bounded214 (domain_from_eq (domain := Cases.C021.initial 214) (congrArg (Sign.withNegation globalNegation) hnode214) (Eq.refl Bool.true))
  let bounded216 := below_succ bounded215 (domain_from_eq (domain := Cases.C021.initial 215) (congrArg (Sign.withNegation globalNegation) hnode215) (Eq.refl Bool.true))
  let bounded217 := below_succ bounded216 (top_allows (Sign.withNegation globalNegation (assignment 216)))
  let bounded218 := below_succ bounded217 (domain_from_eq (domain := Cases.C021.initial 217) (congrArg (Sign.withNegation globalNegation) hnode217) (Eq.refl Bool.true))
  let bounded219 := below_succ bounded218 (domain_from_eq (domain := Cases.C021.initial 218) (congrArg (Sign.withNegation globalNegation) hnode218) (Eq.refl Bool.true))
  let bounded220 := below_succ bounded219 (top_allows (Sign.withNegation globalNegation (assignment 219)))
  let bounded221 := below_succ bounded220 (domain_from_eq (domain := Cases.C021.initial 220) (congrArg (Sign.withNegation globalNegation) hnode220) (Eq.refl Bool.true))
  let bounded222 := below_succ bounded221 (domain_from_eq (domain := Cases.C021.initial 221) (congrArg (Sign.withNegation globalNegation) hnode221) (Eq.refl Bool.true))
  let bounded223 := below_succ bounded222 (domain_from_eq (domain := Cases.C021.initial 222) (congrArg (Sign.withNegation globalNegation) hnode222) (Eq.refl Bool.true))
  let bounded224 := below_succ bounded223 (domain_from_eq (domain := Cases.C021.initial 223) (congrArg (Sign.withNegation globalNegation) hnode223) (Eq.refl Bool.true))
  let bounded225 := below_succ bounded224 (domain_from_eq (domain := Cases.C021.initial 224) (congrArg (Sign.withNegation globalNegation) hnode224) (Eq.refl Bool.true))
  let bounded226 := below_succ bounded225 (domain_from_eq (domain := Cases.C021.initial 225) (congrArg (Sign.withNegation globalNegation) hnode225) (Eq.refl Bool.true))
  let bounded227 := below_succ bounded226 (domain_from_eq (domain := Cases.C021.initial 226) (congrArg (Sign.withNegation globalNegation) hnode226) (Eq.refl Bool.true))
  let bounded228 := below_succ bounded227 (domain_from_eq (domain := Cases.C021.initial 227) (congrArg (Sign.withNegation globalNegation) hnode227) (Eq.refl Bool.true))
  let bounded229 := below_succ bounded228 (top_allows (Sign.withNegation globalNegation (assignment 228)))
  let bounded230 := below_succ bounded229 (domain_from_eq (domain := Cases.C021.initial 229) (congrArg (Sign.withNegation globalNegation) hnode229) (Eq.refl Bool.true))
  let bounded231 := below_succ bounded230 (domain_from_eq (domain := Cases.C021.initial 230) (congrArg (Sign.withNegation globalNegation) hnode230) (Eq.refl Bool.true))
  let bounded232 := below_succ bounded231 (top_allows (Sign.withNegation globalNegation (assignment 231)))
  let bounded233 := below_succ bounded232 (domain_from_eq (domain := Cases.C021.initial 232) (congrArg (Sign.withNegation globalNegation) hnode232) (Eq.refl Bool.true))
  let bounded234 := below_succ bounded233 (domain_from_eq (domain := Cases.C021.initial 233) (congrArg (Sign.withNegation globalNegation) hnode233) (Eq.refl Bool.true))
  let bounded235 := below_succ bounded234 (domain_from_eq (domain := Cases.C021.initial 234) (congrArg (Sign.withNegation globalNegation) hnode234) (Eq.refl Bool.true))
  let bounded236 := below_succ bounded235 (domain_from_eq (domain := Cases.C021.initial 235) (congrArg (Sign.withNegation globalNegation) hnode235) (Eq.refl Bool.true))
  let bounded237 := below_succ bounded236 (domain_from_eq (domain := Cases.C021.initial 236) (congrArg (Sign.withNegation globalNegation) hnode236) (Eq.refl Bool.true))
  let bounded238 := below_succ bounded237 (domain_from_eq (domain := Cases.C021.initial 237) (congrArg (Sign.withNegation globalNegation) hnode237) (Eq.refl Bool.true))
  let bounded239 := below_succ bounded238 (domain_from_eq (domain := Cases.C021.initial 238) (congrArg (Sign.withNegation globalNegation) hnode238) (Eq.refl Bool.true))
  let bounded240 := below_succ bounded239 (top_allows (Sign.withNegation globalNegation (assignment 239)))
  let bounded241 := below_succ bounded240 (top_allows (Sign.withNegation globalNegation (assignment 240)))
  let bounded242 := below_succ bounded241 (domain_from_eq (domain := Cases.C021.initial 241) (congrArg (Sign.withNegation globalNegation) hnode241) (Eq.refl Bool.true))
  let bounded243 := below_succ bounded242 (domain_from_eq (domain := Cases.C021.initial 242) (congrArg (Sign.withNegation globalNegation) hnode242) (Eq.refl Bool.true))
  let bounded244 := below_succ bounded243 (domain_from_eq (domain := Cases.C021.initial 243) (congrArg (Sign.withNegation globalNegation) hnode243) (Eq.refl Bool.true))
  let bounded245 := below_succ bounded244 (domain_from_eq (domain := Cases.C021.initial 244) (congrArg (Sign.withNegation globalNegation) hnode244) (Eq.refl Bool.true))
  let bounded246 := below_succ bounded245 (domain_from_eq (domain := Cases.C021.initial 245) (congrArg (Sign.withNegation globalNegation) hnode245) (Eq.refl Bool.true))
  let bounded247 := below_succ bounded246 (top_allows (Sign.withNegation globalNegation (assignment 246)))
  let bounded248 := below_succ bounded247 (top_allows (Sign.withNegation globalNegation (assignment 247)))
  let bounded249 := below_succ bounded248 (top_allows (Sign.withNegation globalNegation (assignment 248)))
  let bounded250 := below_succ bounded249 (top_allows (Sign.withNegation globalNegation (assignment 249)))
  let bounded251 := below_succ bounded250 (top_allows (Sign.withNegation globalNegation (assignment 250)))
  let bounded252 := below_succ bounded251 (top_allows (Sign.withNegation globalNegation (assignment 251)))
  bounded252

theorem support_sign_contradiction (assignment : Nat → Sign)
    (h_anchor : Eq (assignment anchor) Sign.positive)
    (h_support : SupportEquations assignment) (h_zero : ZeroEquations assignment)
    (h_gp : Data.ValidUsedRelations assignment) : False :=
  Cases.C021.abstract_sign_contradiction
    (fun index => Sign.withNegation globalNegation (assignment index))
    (initial_domains_sound assignment h_anchor h_support h_zero)
    (Data.ValidUsedRelations.with_global_negation h_gp globalNegation)
end Papers.RationalityTen.PureGP.Initializers.C021
#print axioms Papers.RationalityTen.PureGP.Initializers.C021.support_sign_contradiction
