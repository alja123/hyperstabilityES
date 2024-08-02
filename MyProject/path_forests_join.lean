import MyProject

import MyProject.path_forests
  --import MyProject.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 600000

universe u
variable {V : Type u} {G : SimpleGraph V}
variable  [FinV: Fintype V]
variable  [DecG: DecidableRel G.Adj]
variable  [FinV2: Fintype (Sym2 V)]
variable {p m κ pr h γ α : ℕ}
variable {κPositive: κ >0}
variable {pPositive: p >0}
variable {mPositive: m >0}
variable {hPositive: h >0}
variable {prPositive: pr >0}
variable {γPositive: γ >0}
variable (iI:Inhabited (Clump G p m κ pr h))
variable (iV:Inhabited V)
variable (iSub:Inhabited (Subgraph G))
variable (iSP:Inhabited (SubgraphPath_implicit   G) )

variable {prggp: pr≫ p}
variable {mggpr: m≫ pr}



def tail_disjoint_imp
--(H: Subgraph G)
(P1 P2: SubgraphPath_implicit G)
:=
(P1.Pa.Wa.support).Disjoint (P2.Pa.Wa.support.tail)




lemma join_three_paths
(H: Subgraph G)
(P1 P2 P3: SubgraphPath_implicit G)
(a d: V)
(H1: P1.H≤ H)
(H2: P2.H≤ H)
(H3: P3.H≤ H)
(ha: a=P1.s)
(hd: d=P3.e)
(hP1_P2: P1.e=P2.s)
(hP2_P3: P2.e=P3.s)
--(hP3_P1: P3.e=P1.s)
(disj_P1_P2: tail_disjoint_imp   P1 P2)
(disj_P2_P3: tail_disjoint_imp   P2 P3)
--(disj_P3_P1: tail_disjoint_imp   P3 P1)
(disj_P1_P3: tail_disjoint_imp   P1 P3)
:
∃ (P: SubgraphPath H a d),
P.Wa.support=P1.Pa.Wa.support++P2.Pa.Wa.support.tail++P3.Pa.Wa.support.tail
∧ {v:V|v∈ P.Wa.support}= {v:V|v∈ P1.Pa.Wa.support} ∪ {v:V|v∈ P2.Pa.Wa.support} ∪ {v:V|v∈ P3.Pa.Wa.support}
:= by
--let a:V:=P1.s
let b:V:=P1.e
let c:V:=P2.e
--let d:V:=P3.e
--have hb: b=P2.s:= by exact hP1_P2
--have hb: b=P1.e:= by exact rfl
--rw[hP1_P2] at b

have Q1ex: ∃ (Q1: Walk G a b), Q1.toSubgraph = P1.Pa.Wa.toSubgraph∧ Q1.support=P1.Pa.Wa.support∧ 1=1:= by
  dsimp [b,c]
  rw[ha]
  use P1.Pa.Wa

have Q2ex: ∃ (Q2: Walk G b c), Q2.toSubgraph = P2.Pa.Wa.toSubgraph∧ Q2.support=P2.Pa.Wa.support∧ 1=1:= by
  dsimp [b,c]
  rw[hP1_P2]
  use P2.Pa.Wa

have Q3ex: ∃ (Q3: Walk G c d), Q3.toSubgraph = P3.Pa.Wa.toSubgraph∧ Q3.support=P3.Pa.Wa.support∧ 1=1:= by
  dsimp [c]
  rw[hd]
  rw[hP2_P3]
  use P3.Pa.Wa



rcases Q1ex with ⟨Q1, ⟨sQ1, ⟨eQ1 , hQ1⟩ ⟩ ⟩
rcases Q2ex with ⟨Q2, ⟨sQ2, ⟨eQ2 , hQ2⟩ ⟩ ⟩
rcases Q3ex with ⟨Q3, ⟨sQ3, ⟨eQ3 , hQ3⟩ ⟩ ⟩


let W12: Walk G a c:=Q1.append Q2
let W: Walk G a d:=W12.append Q3


have   W12_Is_Path: W12.IsPath:= by
  dsimp[W12]
  refine append_paths a b c Q1 Q2 ?Ppath ?Qpath ?disj
  refine Walk.IsPath.mk' ?Ppath.h
  rw[eQ1]
  refine (Walk.isPath_def P1.Pa.Wa).mp ?Ppath.h.self.support_nodup.a
  exact P1.Pa.Wa_Is_Path

  refine Walk.IsPath.mk' ?Qpath.h
  rw[eQ2]
  refine (Walk.isPath_def P2.Pa.Wa).mp ?Qpath.h.self.support_nodup.a
  exact P2.Pa.Wa_Is_Path

  rw[eQ1, eQ2]
  unfold tail_disjoint_imp at disj_P1_P2
  exact disj_P1_P2

have   W_Is_Path: W.IsPath:= by
  dsimp[W]
  apply append_paths
  exact W12_Is_Path
  apply Walk.IsPath.mk'
  rw[eQ3]
  refine (Walk.isPath_def P3.Pa.Wa).mp ?Qpath.h.a
  exact P3.Pa.Wa_Is_Path

  dsimp[W12]
  refine List.disjoint_left.mpr ?disj.a
  intro v hv
  simp at hv
  rcases hv with hh|hhh
  rw[eQ3]
  rw[eQ1] at hh
  unfold  tail_disjoint_imp at disj_P1_P3
  exact disj_P1_P3 hh

  rw[eQ3]
  rw[eQ2] at hhh
  unfold  tail_disjoint_imp at disj_P2_P3
  exact disj_P2_P3 hhh



have   Wa_In_H: W.toSubgraph≤ H:= by
  dsimp[W, W12]
  simp
  rw[sQ1, sQ2, sQ3]
  constructor
  constructor
  have h1: _:= by exact P1.Pa.Wa_In_H
  exact Preorder.le_trans P1.Pa.Wa.toSubgraph P1.H H h1 H1
  have h2: _:= by exact P2.Pa.Wa_In_H
  exact Preorder.le_trans P2.Pa.Wa.toSubgraph P2.H H h2 H2
  have h3: _:= by exact P3.Pa.Wa_In_H
  exact Preorder.le_trans P3.Pa.Wa.toSubgraph P3.H H h3 H3


let P: SubgraphPath H a d:=⟨W, W_Is_Path, Wa_In_H⟩

use P

constructor

dsimp [W]
dsimp[W12]
simp
rw [@Walk.support_append]
rw [@Walk.support_append]
rw[eQ1, eQ2, eQ3]



simp
ext v
constructor
intro h
simp
dsimp [W] at h
dsimp[W12] at h
simp at h
rw[eQ1, eQ2, eQ3] at h
exact h

intro h
simp
dsimp [W]
dsimp[W12]
simp
rw[eQ1, eQ2, eQ3]
exact h





def tail_disjoint_forest
(H: Subgraph G)
(F1 F2: PathForest iV iSP H)
:=
∀(P1 P2: SubgraphPath_implicit G),
P1∈ F1.P→
P2∈ F2.P→
tail_disjoint_imp  (P1) (P2)--(P1.Pa.Wa.support).Disjoint (P2.Pa.Wa.support.tail)





def Path_forest_support_until_t
{H: Subgraph G}
(Fo: PathForest iV iSP H)
(t:ℕ )
: Set V
:={v: V| ∃ (i: ℕ ), i<t∧  (v∈ (Fo.P.get! i).Pa.Wa.support)}


lemma path_forest_support_add_one
{H: Subgraph G}
(Fo: PathForest iV iSP H)
(t:ℕ )
:
Path_forest_support_until_t iV iSP  Fo (t+1)=Path_forest_support_until_t iV iSP  Fo t ∪ {v: V|v∈ (Fo.P.get! t).Pa.Wa.support}
:= by
unfold Path_forest_support_until_t
ext v
constructor
intro h1
simp
simp at h1
rcases h1 with ⟨i, ⟨ h1, h2⟩ ⟩
by_cases cas: i=t
right
rw[cas] at h2
exact h2

simp at cas
left
use i
constructor
have h4:i≤ t:= by
  exact Nat.le_of_lt_succ h1
exact Nat.lt_of_le_of_ne h4 cas
exact h2

intro h
simp
simp at h
rcases h with h1|h2
rcases h1 with ⟨i, ⟨ hi1, hi2⟩ ⟩
use i
constructor
exact Nat.lt_add_right 1 hi1
exact hi2

use t
constructor
exact lt_add_one t
exact h2



lemma join_three_forests
(H: Subgraph G)
(F1 F2 F3: PathForest iV iSP H)
--(S1 S2 S3: Set V)
(hF1_F2: F1.E=F2.S)
(hF2_F3: F2.E=F3.S)
(hF3_F1: F3.E=F1.S.tail)
(disj_F1_F2: tail_disjoint_forest iV iSP H F1 F2)
(disj_F2_F1: tail_disjoint_forest iV iSP H F2 F1)

(disj_F2_F3: tail_disjoint_forest iV iSP H F2 F3)
(disj_F3_F1: tail_disjoint_forest iV iSP H F3 F1)
(disj_F1_F3: tail_disjoint_forest iV iSP H F1 F3)

(t: ℕ )
(pos1: 0<F1.k)
(pos2: 0<F2.k)
(pos3: 0<F3.k)


:
∃ (P: SubgraphPath H (F1.S.get! 0) (F3.E.get! (t))),
{v:V|v∈ P.Wa.support}=Path_forest_support_until_t iV iSP  F1 (t+1)∪ Path_forest_support_until_t iV iSP  F2 (t+1)∪ Path_forest_support_until_t iV iSP  F3 (t+1)

:= by


have F1PGet: ∀ (i:ℕ), (i< F1.P.length)→  (F1.P.get! i ∈ F1.P):=by
  intro i hi
  simp
  have h2:F1.P.getD i default=F1.P.get ⟨i, hi ⟩:= by exact List.getD_eq_get F1.P default hi
  rw[h2]
  exact List.get_mem F1.P i hi



induction' t with t IH
simp

have hex: _:= by
  apply  join_three_paths H (F1.P.get! 0) (F2.P.get! 0) (F3.P.get! 0) (F1.S.get! 0) (F3.E.get! (0))
  apply  F1.Graphs_equal 0 pos1
  apply  F2.Graphs_equal 0 pos2
  apply  F3.Graphs_equal 0 pos3

  apply F1.Starts_equal
  exact pos1

  apply F3.Ends_equal; exact pos3


  have h1:  (F1.P.get! 0).e=F1.E.get! 0:=by
    symm
    apply F1.Ends_equal
    exact pos1
  rw[h1]
  have h1:  (F2.P.get! 0).s=F2.S.get! 0:=by
    symm
    apply F2.Starts_equal
    exact pos2
  rw[h1]
  rw[hF1_F2]


  have h1:  (F2.P.get! 0).e=F2.E.get! 0:=by
    symm;    apply F2.Ends_equal;    exact pos2
  rw[h1]
  have h1:  (F3.P.get! 0).s=F3.S.get! 0:=by
    symm;    apply F3.Starts_equal;    exact pos3
  rw[h1, hF2_F3]

  apply disj_F1_F2


  apply F1PGet
  rw [F1.P_length]; exact pos1

  --same as prev
  sorry


  unfold tail_disjoint_forest at disj_F2_F3
  apply disj_F2_F3
  --same as prev
  sorry
  --same as prev
  sorry

  apply disj_F1_F3
  --same as prev
  sorry
  --same as prev
  sorry



rcases hex with ⟨P, ⟨ hP1, hP2⟩ ⟩

use P

rw[hP2]
unfold Path_forest_support_until_t

ext v
constructor
intro h
simp
simp at h
exact h

intro h
simp
simp at h
exact h



--induction-------------------------------------



have hdisj12: ∀(i j: ℕ ), (i< t+2)→ (i<t+2)→ (tail_disjoint_imp (F1.P.get! i) (F2.P.get! j)):= by
  sorry
have hdisj21: ∀(i j: ℕ ), (i< t+2)→ (i<t+2)→ (tail_disjoint_imp (F2.P.get! i) (F1.P.get! j)):= by
  sorry
have hdisj13: ∀(i j: ℕ ), (i< t+2)→ (i<t+2)→ (tail_disjoint_imp (F1.P.get! i) (F3.P.get! j)):= by
  sorry
have hdisj23: ∀(i j: ℕ ), (i< t+2)→ (i<t+2)→ (tail_disjoint_imp (F2.P.get! i) (F3.P.get! j)):= by
  sorry



have pos1: t+1<F1.k:= by sorry
have pos2: t+1<F2.k:= by sorry
have pos3: t+1<F3.k:= by sorry

have hex: _:= by
  apply  join_three_paths H (F1.P.get! (t+1)) (F2.P.get! (t+1)) (F3.P.get! (t+1)) (F3.E.get! t) (F3.E.get! ((t+1)))
  apply  F1.Graphs_equal (t+1) pos1
  apply  F2.Graphs_equal (t+1) pos2
  apply  F3.Graphs_equal (t+1) pos3

  sorry

  sorry

  sorry
  /-have h1:  (F1.P.get! 0).e=F1.E.get! 0:=by
    symm
    apply F1.Ends_equal
    exact pos1
  rw[h1]
  have h1:  (F2.P.get! 0).s=F2.S.get! 0:=by
    symm
    apply F2.Starts_equal
    exact pos2
  rw[h1]
  rw[hF1_F2]-/

  sorry--like previous block

  apply disj_F1_F2
  simp
  sorry
  sorry

  sorry

  sorry


rcases IH with ⟨P, hP1 ⟩
rcases hex with ⟨Q, ⟨ hQ1, hQ2⟩ ⟩

let RWa: Walk G (F1.S.get! 0) (F3.E.get! (t+1)):=P.Wa.append Q.Wa
have RWa_Is_Path: RWa.IsPath:= by
  dsimp[RWa]
  apply append_paths --(F1.S.get! 0) (F3.E.get! t) (F3.E.get! (t + 1)) P.Wa Q.Wa ?Ppath ?Qpath ?disj
  exact P.Wa_Is_Path
  exact Q.Wa_Is_Path

  intro x hp
  simp
  have hp1: x ∈ {v:V|v∈ P.Wa.support}:=by simp; exact hp
  rw[hP1] at hp1
  simp at hp1
  rw[hQ1]
  simp


  rw [List.tail_append_of_ne_nil]
  simp
  constructor
  rcases hp1 with c1|c2
  rcases c1 with c3|c4

  --
  sorry
  unfold Path_forest_support_until_t at c4
  unfold tail_disjoint_forest at disj_F2_F1
  simp at c4
  rcases c4 with ⟨ i, ⟨ hi1, hi2⟩ ⟩
  apply disj_F2_F1
  have h4: F2.P.get! i∈ F2.P:= by sorry
  exact h4
  --F1.P.get! (t + 1) ∈ F1.P
  sorry
  exact hi2


  --
  sorry

  constructor

  sorry
  sorry

  --(F1.P.get! (t + 1)).Pa.Wa.support ≠ []
  sorry
  --



  --have hq1: x ∉  {v:V|v∈ Q.Wa.support.tail}:=by
  --  rw[hP1] at hp1
  --  simp at hp1

  --sorry

have RWa_In_H: RWa.toSubgraph≤ H:= by
  dsimp[RWa]
  simp
  constructor
  exact P.Wa_In_H
  exact Q.Wa_In_H


let R: SubgraphPath H (F1.S.get! 0) (F3.E.get! (t+1)):=⟨RWa, RWa_Is_Path, RWa_In_H⟩

use R

rw[path_forest_support_add_one _ _  F1]
rw[path_forest_support_add_one _ _  F2]
rw[path_forest_support_add_one _ _  F3]

dsimp [R]
dsimp [RWa]

simp
have h5:  {v | v ∈ P.Wa.support ∨ v ∈ Q.Wa.support}= {v | v ∈ P.Wa.support} ∪ {v | v ∈ Q.Wa.support}:= by
  exact rfl
rw[h5]
rw[hP1, hQ2]


sorry--aesop

/-simp only [Walk.mem_support_append_iff]
have h5:  {v | v ∈ P.Wa.support ∨ v ∈ Q.Wa.support}= {v | v ∈ P.Wa.support} ∪ {v | v ∈ Q.Wa.support}:= by
  sorry
rw[h5]
rw[hP1, hQ2]

unfold Path_forest_support_until_t
ext v
constructor
intro h
simp
simp at h

aesop
-/

--#check SimpleGraph.append_paths



/-
structure SubgraphPath_implicit
(G: SimpleGraph V) where
  H: Subgraph G
  s: V
  e: V
  Pa: SubgraphPath H s e



variable (iSP:Inhabited (SubgraphPath_implicit   G) )



def starts_equal
(S : List V)
(P: List (SubgraphPath_implicit G))
(k: ℕ )
:=∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).s)


def ends_equal
(E : List V)
(P: List (SubgraphPath_implicit G))
(k: ℕ )
:=∀ (i: ℕ ), i< k→ ((E.get! i)=(P.get! i).e)

def graphs_equal
(H : Subgraph G)
(P: List (SubgraphPath_implicit G))
(k: ℕ )
:=∀ (i: ℕ ), i< k→ ((P.get! i).H≤ H)


def paths_disjoint
 (P: List (SubgraphPath_implicit G))
(k: ℕ )
:=∀ (i j: ℕ ), i< j→ j< k→ (Disjoint {v:V|v∈ (P.get! i).Pa.Wa.support} {v:V|v∈ (P.get! j).Pa.Wa.support})


structure PathForest (H: Subgraph G)--(G: SimpleGraph V)(iSP:Inhabited (SubgraphPath_implicit G))
where
  (S E: List V)
  (P: List (SubgraphPath_implicit G))
  (k: ℕ )
  (Starts_equal: starts_equal iV iSP S P k)--∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).s))
  (Ends_equal: ends_equal iV iSP E P k)--∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).e))
  (Graphs_equal: graphs_equal iSP H P k)--∀ (i: ℕ ), i< k→ (P.get! i).H=H)
  (Paths_disjoint: paths_disjoint iSP  P k)  --(disjoint: ∀ (i j: ℕ ), i< k→ j< k→ i≠ j→ (List.Disjoint ((P.get! i).Pa.Wa.support) ((P.get! j).Pa.Wa.support)))
  (P_length: P.length=k)

def Path_forest_support
{H: Subgraph G}
(Fo: PathForest iV iSP H)
: Set V
:={v: V| ∃ (Pi: SubgraphPath_implicit G), Pi∈ Fo.P∧  (v∈ Pi.Pa.Wa.support)}


def Path_forest_avoids
{H: Subgraph G}
(Fo: PathForest iV iSP H)
(Fb: Set V)
:=
∀ (i: ℕ ), i< Fo.k→ (Disjoint {v:V|v∈ (Fo.P.get! i).Pa.Wa.support} Fb)

def Path_forest_avoids_list
{H: Subgraph G}
(Fo: PathForest iV iSP H)
(Fb: List V)
:=
∀ (i: ℕ ), i< Fo.k→ (List.Disjoint ((Fo.P.get! i).Pa.Wa.support) Fb)


def cut_dense_list
(HL: List (Subgraph G))
(p: ℕ )
:=∀(i: Fin (HL.length)),  (cut_dense G  (HL.get i) p)

def small_intersection_list
(HL: List (Subgraph G))
(Fb: Set V)
(p e: ℕ )
--(k: ℕ )
:=∀(i: Fin (HL.length)),
(8*p*
(Fb∩ (HL.get i).verts).toFinset.card+e≤ (HL.get i).verts.toFinset.card
)

def vertex_list_in_graph_list
(S: List V)
(HL: List (Subgraph G))
(k: ℕ )
:=∀ (i: ℕ ), i< k→ (S.get! i)∈ (HL.get! i).verts


def vertex_list_outside_set
(S: List V)
(Fb: Set V)
(k: ℕ )
:=∀ (i: ℕ ), i< k→ (S.get! i)∉ Fb

structure SubgraphWalk
(H: Subgraph G) (u v: V) where
  Wa: G.Walk u v
  Wa_In_H: Wa.toSubgraph≤ H

structure SubgraphPath
(H: Subgraph G) (u v: V) where
  Wa: G.Walk u v
  Wa_Is_Path: Wa.IsPath
  Wa_In_H: Wa.toSubgraph≤ H

-/
