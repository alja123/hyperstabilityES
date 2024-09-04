import MyProject

import MyProject.path.find_path_forest
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




/-
def tail_disjoint_forest
(H: Subgraph G)
(F1 F2: PathForest' iV iSP H)
:=
∀(P1 P2: SubgraphPath_implicit G),
P1∈ F1.P→
P2∈ F2.P→
tail_disjoint_imp  (P1) (P2)--(P1.Pa.Wa.support).Disjoint (P2.Pa.Wa.support.tail)
-/




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




---------------------------------------------------------------------------









lemma join_three_forests_tail_disjoint
(H: Subgraph G)
(F1 F2 F3: PathForest iV iSP H)
--(S1 S2 S3: Set V)
(hF1_F2: F1.E=F2.S)
(hF2_F3: F2.E=F3.S)
(hF3_F1: F3.E=F1.S.rotate 1)
--(disj_F1_F2: tail_disjoint_forest iV iSP H F1 F2)
--(disj_F2_F1: tail_disjoint_forest iV iSP H F2 F1)

--(disj_F2_F3: tail_disjoint_forest iV iSP H F2 F3)
--(disj_F3_F1: tail_disjoint_forest iV iSP H F3 F1)
--(disj_F1_F3: tail_disjoint_forest iV iSP H F1 F3)
(t tmax: ℕ )

( hdisj11: ∀(i j: ℕ ), (i< j)→ (j<tmax)→ (tail_disjoint_imp (F1.P.get! i) (F1.P.get! j)))
( hdisj22: ∀(i j: ℕ ), (i< j)→ (j<tmax)→ (tail_disjoint_imp (F2.P.get! i) (F2.P.get! j)))
( hdisj33: ∀(i j: ℕ ), (i< j)→ (j<tmax)→ (tail_disjoint_imp (F3.P.get! i) (F3.P.get! j)))

( hdisj12: ∀(i j: ℕ ), (i< tmax)→ (j<tmax)→ (tail_disjoint_imp (F1.P.get! i) (F2.P.get! j)))
( hdisj23: ∀(i j: ℕ ), (i< tmax)→ (j<tmax)→ (tail_disjoint_imp (F2.P.get! i) (F3.P.get! j)))
( hdisj31: ∀(i j: ℕ ), (i< tmax)→ (j<tmax)→ (tail_disjoint_imp (F3.P.get! i) (F1.P.get! j)))


( hdisj21: ∀(i j: ℕ ), (i< tmax)→ (j<tmax)→ (i≠ j)→ (tail_disjoint_imp (F2.P.get! i) (F1.P.get! j)))
( hdisj13: ∀(i j: ℕ ), (i< tmax)→ (j<tmax)→ (i≠ j+1)→ (tail_disjoint_imp (F1.P.get! i) (F3.P.get! j)))
( hdisj32: ∀(i j: ℕ ), (i< tmax)→ (j<tmax)→ (i≠ j)→ (tail_disjoint_imp (F3.P.get! i) (F2.P.get! j)))

(Slength: tmax < F1.S.length)

(ht: t<tmax)
(pos1: tmax<F1.k)
(pos2: tmax<F2.k)
(pos3: tmax<F3.k)


:
∃ (P: SubgraphPath H (F1.S.get! 0) (F3.E.get! (t))),
{v:V|v∈ P.Wa.support}=Path_forest_support_until_t iV iSP  F1 (t+1)∪ Path_forest_support_until_t iV iSP  F2 (t+1)∪ Path_forest_support_until_t iV iSP  F3 (t+1)

:= by
sorry/-

have F1PGet: ∀ (i:ℕ), (i< F1.P.length)→  (F1.P.get! i ∈ F1.P):=by
  intro i hi
  simp
  have h2:F1.P.getD i default=F1.P.get ⟨i, hi ⟩:= by exact List.getD_eq_get F1.P default hi
  rw[h2]
  exact List.get_mem F1.P i hi



induction' t with t IH
simp

have pos1: 0<F1.k:= by
  exact Nat.zero_lt_of_lt pos1
have pos2: 0<F2.k:= by
  exact Nat.zero_lt_of_lt pos2
have pos3: 0<F3.k:= by
  exact Nat.zero_lt_of_lt pos3


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

  apply hdisj12; exact ht; exact ht
  apply hdisj23; exact ht; exact ht
  apply hdisj13; exact ht; exact ht;  exact Nat.zero_ne_add_one 0



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


have hdisj11: ∀(i j: ℕ ), (i< j)→ (j<t+2)→ (tail_disjoint_imp (F1.P.get! i) (F1.P.get! j)):= by
  intro i j hi hj;  apply hdisj11; exact hi; exact Nat.lt_of_lt_of_le hj ht
have hdisj22: ∀(i j: ℕ ), (i< j)→ (j<t+2)→ (tail_disjoint_imp (F2.P.get! i) (F2.P.get! j)):= by
  intro i j hi hj;  apply hdisj22; exact hi; exact Nat.lt_of_lt_of_le hj ht
have hdisj33: ∀(i j: ℕ ), (i< j)→ (j<t+2)→ (tail_disjoint_imp (F3.P.get! i) (F3.P.get! j)):= by
  intro i j hi hj;  apply hdisj33; exact hi; exact Nat.lt_of_lt_of_le hj ht

have hdisj12: ∀(i j: ℕ ), (i< t+2)→ (j<t+2)→ (tail_disjoint_imp (F1.P.get! i) (F2.P.get! j)):= by
  intro i j hi hj;  apply hdisj12; exact Nat.lt_of_lt_of_le hi ht; exact Nat.lt_of_lt_of_le hj ht
have hdisj23: ∀(i j: ℕ ), (i< t+2)→ (j<t+2)→ (tail_disjoint_imp (F2.P.get! i) (F3.P.get! j)):= by
  intro i j hi hj;  apply hdisj23; exact Nat.lt_of_lt_of_le hi ht; exact Nat.lt_of_lt_of_le hj ht
have hdisj31: ∀(i j: ℕ ), (i< t+2)→ (j<t+2)→ (tail_disjoint_imp (F3.P.get! i) (F1.P.get! j)):= by
  intro i j hi hj;  apply hdisj31; exact Nat.lt_of_lt_of_le hi ht; exact Nat.lt_of_lt_of_le hj ht

have hdisj21: ∀(i j: ℕ ), (i< t+2)→ (j<t+2)→ (i≠ j)→ (tail_disjoint_imp (F2.P.get! i) (F1.P.get! j)):= by
  intro i j hi hj;  apply hdisj21; exact Nat.lt_of_lt_of_le hi ht; exact Nat.lt_of_lt_of_le hj ht
have hdisj32: ∀(i j: ℕ ), (i< t+2)→ (j<t+2)→ (i≠ j)→ (tail_disjoint_imp (F3.P.get! i) (F2.P.get! j)):= by
  intro i j hi hj;  apply hdisj32; exact Nat.lt_of_lt_of_le hi ht; exact Nat.lt_of_lt_of_le hj ht
have hdisj13: ∀(i j: ℕ ), (i< t+2)→ (j<t+2)→ (i≠ j+1)→ (tail_disjoint_imp (F1.P.get! i) (F3.P.get! j)):= by
  intro i j hi hj;  apply hdisj13; exact Nat.lt_of_lt_of_le hi ht; exact Nat.lt_of_lt_of_le hj ht



have pos1: t+1<F1.k:= by exact Nat.lt_trans ht pos1
have pos2: t+1<F2.k:= by exact Nat.lt_trans ht pos2
have pos3: t+1<F3.k:= by exact Nat.lt_trans ht pos3

have hex: _:= by
  apply  join_three_paths H (F1.P.get! (t+1)) (F2.P.get! (t+1)) (F3.P.get! (t+1)) (F3.E.get! t) (F3.E.get! ((t+1)))
  apply  F1.Graphs_equal (t+1) pos1
  apply  F2.Graphs_equal (t+1) pos2
  apply  F3.Graphs_equal (t+1) pos3

  rw [hF3_F1]
  have h1: F1.S.tail.get! t=F1.S.get! (t+1):=by
    simp
    have h2: F1.S=F1.S.drop 0:= by exact rfl
    rw[h2]
    rw[List.tail_drop]
    simp only [zero_add]
    rw[List.getD_eq_get]
    rw[List.getD_eq_get]


    rw[List.get_drop']
    simp
    simp_rw[add_comm]
    simp

    refine Nat.lt_sub_of_add_lt ?hn.h
    exact Nat.lt_trans ht Slength
    simp
    exact Nat.lt_trans ht Slength

  rw[h1]
  apply F1.Starts_equal (t+1)
  exact pos1

  apply F3.Ends_equal; exact pos3


  have h1:  (F1.P.get! (t+1)).e=F1.E.get! (t+1):=by
    symm
    apply F1.Ends_equal
    exact pos1
  rw[h1]
  have h1:  (F2.P.get! (t+1)).s=F2.S.get! (t+1):=by
    symm
    apply F2.Starts_equal
    exact pos2
  rw[h1]
  rw[hF1_F2]

  have h1:  (F2.P.get! (t+1)).e=F2.E.get! (t+1):=by
    symm
    apply F2.Ends_equal
    exact pos2
  rw[h1]
  have h1:  (F3.P.get! (t+1)).s=F3.S.get! (t+1):=by
    symm
    apply F3.Starts_equal
    exact pos3
  rw[h1]
  rw[hF2_F3]

  apply hdisj12; exact Nat.lt.base (t + 1); exact Nat.lt.base (t + 1);
  apply hdisj23; exact Nat.lt.base (t + 1); exact Nat.lt.base (t + 1);
  apply hdisj13; exact Nat.lt.base (t + 1); exact Nat.lt.base (t + 1);
  exact Ne.symm (Nat.succ_ne_self (t + 1))



have ht':t<tmax:= by exact Nat.lt_of_succ_lt ht
rcases IH ht' with ⟨ P, hP1 ⟩
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

  unfold Path_forest_support_until_t at c3
  simp at c3
  rcases c3 with ⟨ i, ⟨ hi1, hi2⟩ ⟩
  apply hdisj11 i (t+1); exact hi1; exact Nat.lt.base (t + 1); exact hi2

  unfold Path_forest_support_until_t at c4
  simp at c4
  rcases c4 with ⟨ i, ⟨ hi1, hi2⟩ ⟩
  apply hdisj21 i (t+1); exact Nat.lt_succ_of_lt hi1; gcongr; exact Nat.one_lt_two; exact Nat.ne_of_lt hi1
  exact hi2

  unfold Path_forest_support_until_t at c2
  simp at c2
  rcases c2 with ⟨ i, ⟨ hi1, hi2⟩ ⟩
  apply hdisj31 i (t+1); exact Nat.lt_succ_of_lt hi1;  gcongr; exact Nat.one_lt_two;
  exact hi2


  constructor
  rcases hp1 with c1|c1
  rcases c1 with c1|c1

  unfold Path_forest_support_until_t at c1
  simp at c1
  rcases c1 with ⟨ i, ⟨ hi1, hi2⟩ ⟩
  apply hdisj12 i (t+1); exact Nat.lt_succ_of_lt hi1;  gcongr; exact Nat.one_lt_two;
  exact hi2

  unfold Path_forest_support_until_t at c1
  simp at c1
  rcases c1 with ⟨ i, ⟨ hi1, hi2⟩ ⟩
  apply hdisj22 i (t+1); exact hi1; exact Nat.lt.base (t + 1); exact hi2

  unfold Path_forest_support_until_t at c1
  simp at c1
  rcases c1 with ⟨ i, ⟨ hi1, hi2⟩ ⟩
  apply hdisj32 i (t+1); exact Nat.lt_succ_of_lt hi1; gcongr; exact Nat.one_lt_two; exact Nat.ne_of_lt hi1
  exact hi2


  rcases hp1 with c1|c1
  rcases c1 with c1|c1

  unfold Path_forest_support_until_t at c1
  simp at c1
  rcases c1 with ⟨ i, ⟨ hi1, hi2⟩ ⟩
  apply hdisj13 i (t+1); exact Nat.lt_succ_of_lt hi1;  gcongr; exact Nat.one_lt_two;
  linarith
  exact hi2

  unfold Path_forest_support_until_t at c1
  simp at c1
  rcases c1 with ⟨ i, ⟨ hi1, hi2⟩ ⟩
  apply hdisj23 i (t+1); exact Nat.lt_succ_of_lt hi1;  gcongr; exact Nat.one_lt_two;
  exact hi2

  unfold Path_forest_support_until_t at c1
  simp at c1
  rcases c1 with ⟨ i, ⟨ hi1, hi2⟩ ⟩
  apply hdisj33 i (t+1); exact hi1; exact Nat.lt.base (t + 1); exact hi2

  --(F1.P.get! (t + 1)).Pa.Wa.support ≠ []
  exact Walk.support_ne_nil (F1.P.get! (t + 1)).Pa.Wa




  --have hq1: x ∉  {v:V|v∈ Q.Wa.support.tail}:=by
  --  rw[hP1] at hp1
  --  simp at hp1

  --

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
aesop


-/
