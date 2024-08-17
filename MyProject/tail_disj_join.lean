import MyProject

import MyProject.tail_disjointness

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats    750000

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





lemma join_three_forests_tail_disjoint
(H: Subgraph G)
(F1 F2 F3: PathForest iV iSP H)
--(S1 S2 S3: Set V)
(hF1_F2: F1.E=F2.S)
(hF2_F3: F2.E=F3.S)
(hF3_F1: F3.E=F1.S.tail)
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


have F1PGet: ∀ (i:ℕ), (i< F1.P.length)→  (F1.P.get! i ∈ F1.P):=by
  intro i hi
  simp
  have h2:F1.P.getD i default=F1.P.get ⟨i, hi ⟩:= by exact List.getD_eq_get F1.P default hi
  rw[h2]
  exact List.get_mem F1.P i hi



induction' t with t IH
simp

have pos1: 0<F1.k:= by exact Nat.zero_lt_of_lt pos1
have pos2: 0<F2.k:= by exact Nat.zero_lt_of_lt pos2
have pos3: 0<F3.k:= by exact Nat.zero_lt_of_lt pos3

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
  sorry



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
 
