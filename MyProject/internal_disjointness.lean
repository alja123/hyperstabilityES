import MyProject

import MyProject.path_forests_clump_sequence_preparation
--C:\Users\alja1\Downloads\pro\my_project\MyProject\path_forests_clump_sequence_preparation.lean
open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats   250000

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





def interior
{u v: V}
(W: Walk G u v )
: Set V:=
{x: V| x∈ W.support∧ x≠ u ∧ x≠ v}



def internally_disjoint
(P1 P2: SubgraphPath_implicit G)
:=
 (interior P1.Pa.Wa)∩  (interior P2.Pa.Wa)= ∅




/-structure PathForest (H: Subgraph G)--(G: SimpleGraph V)(iSP:Inhabited (SubgraphPath_implicit G))
where
  (S E: List V)
  (P: List (SubgraphPath_implicit G))
  (k: ℕ )
  (Starts_equal: starts_equal iV iSP S P k)--∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).s))
  (Ends_equal: ends_equal iV iSP E P k)--∀ (i: ℕ ), i< k→ ((S.get! i)=(P.get! i).e))
  (Graphs_equal: graphs_equal iSP H P k)--∀ (i: ℕ ), i< k→ (P.get! i).H=H)
  (Paths_disjoint: paths_disjoint iSP  P k)  --(disjoint: ∀ (i j: ℕ ), i< k→ j< k→ i≠ j→ (List.Disjoint ((P.get! i).Pa.Wa.support) ((P.get! j).Pa.Wa.support)))
  (P_length: P.length=k)-/



lemma Path_forest_starts_inter
(F: PathForest iV iSP H)
--(P: SubgraphPath_implicit G)
(i: ℕ )
(hi: i< F.k)
--(v: V)
--(hv: v ∈ P.Pa.Wa.support)
(hk: F.k=F.S.length)
:
F.S.get! i∈ (F.P.get! i).Pa.Wa.support
:= by

sorry

lemma Path_forest_starts_inter2
(F: PathForest iV iSP H)
--(P: SubgraphPath_implicit G)
(i j: ℕ )
(hi: i< F.k)
(hj: j< F.k)
(hij: i< j)
--(v: V)
--(hv: v ∈ P.Pa.Wa.support)
(hk: F.k=F.S.length)
:
F.S.get! j∉  (F.P.get! i).Pa.Wa.support
:= by
by_contra cont
have hhi:  F.S.get! j∈  (F.P.get! j).Pa.Wa.support:= by
  apply Path_forest_starts_inter
  exact hj
  exact hk

have hdisj: _:= by exact F.Paths_disjoint
unfold paths_disjoint at hdisj

have hdisj2: _:= by exact hdisj i j hij hj
have neg: ¬ (Disjoint {v | v ∈ (F.P.get! i).Pa.Wa.support} {v | v ∈ (F.P.get! j).Pa.Wa.support})
:= by
  refine Set.not_disjoint_iff.mpr ?_
  use F.S.get! j
  constructor
  simp only [Set.mem_setOf_eq]
  exact cont

  simp only [Set.mem_setOf_eq]
  exact hhi
exact neg (hdisj i j hij hj)



lemma Path_forest_starts_inter3
(F: PathForest iV iSP H)
--(P: SubgraphPath_implicit G)
(i j: ℕ )
(hi: i< F.k)
(hj: j< F.k)
(hij: i≠  j)
--(v: V)
--(hv: v ∈ P.Pa.Wa.support)
(hk: F.k=F.S.length)
:
F.S.get! j∉  (F.P.get! i).Pa.Wa.support
:= by
sorry


lemma Path_forest_starts_aux_get
(F: PathForest iV iSP H)
(i: ℕ )
(hi: i< F.k)
(v: V)
(hv: v ∈ (F.P.get! i).Pa.Wa.support)
(hv2: v≠ (F.P.get! i).s)
(hk: F.k=F.S.length)
:
v∉ F.S
:= by
by_contra cont
have hex: ∃ (j: Fin (F.S.length)), F.S.get j=v:= by
  exact List.mem_iff_get.mp cont
rcases hex with ⟨j, hj⟩
have hj': F.S.get! j=v:= by
  sorry
rw[hj'.symm] at hv
have ne: (j:ℕ )≠ i:= by
  by_contra cont2
  have h3: F.S.get! ↑j=(F.P.get! j).s:= by
    apply F.Starts_equal
    sorry
  rw[h3] at hj'
  rw[cont2] at hj'
  rw[hj'] at hv2
  exact hv2 rfl

have hhh: F.S.get! j∉  (F.P.get! i).Pa.Wa.support
:= by
  apply Path_forest_starts_inter3
  repeat assumption
  sorry
  exact ne.symm
  exact hk
exact hhh hv




lemma Path_forest_starts_aux
(F: PathForest iV iSP H)
(P: SubgraphPath_implicit G)
(hP: P ∈ F.P)
(v: V)
(hv: v ∈ P.Pa.Wa.support)
(hv2: v≠ P.s)
(hk: F.k=F.S.length)
:
v∉ F.S
:= by

sorry


lemma set_disjoint_to_internal_disjoint
(F1  F2: PathForest iV iSP H)
(Fb: Set V)
(k: ℕ )
(F1k: F1.k≥ k)
(F2_avoids_Fb: Path_forest_avoids! iV iSP F2 Fb k)
(F1_in_Fb: {v:V| v∈ Path_forest_support iV iSP F1∧ v∉ F1.S∧ v∉ F1.E}= Fb)
(hk: F1.k=F1.S.length)
:
∀(i j: ℕ ), (i< k)→ (j<k)→ (internally_disjoint (F1.P.get! i) (F2.P.get! j))
:= by

intro i j hi hj
unfold internally_disjoint
refine Disjoint.inter_eq ?_
refine Set.disjoint_iff_forall_ne.mpr ?_
unfold interior
intro a ha
intro b hb
simp at ha
simp at hb
let ⟨ha1, ha2, ha3⟩:=ha
let ⟨hb1, hb2, hb3⟩:=hb
unfold Path_forest_avoids! at F2_avoids_Fb
have hx:_:=by exact F2_avoids_Fb j hj
rw[F1_in_Fb.symm] at hx
unfold Path_forest_support at hx
simp at hx
have hbin: b∈{v | v ∈ (F2.P.get! j).Pa.Wa.support} := by
  simp
  exact hb1

have hain: a∈ {v | (∃ Pi ∈ F1.P, v ∈ Pi.Pa.Wa.support) ∧ v ∉ F1.S ∧ v ∉ F1.E}:= by
  simp
  constructor
  use (F1.P.get! i)
  constructor
  sorry
  exact ha1

  constructor
  apply Path_forest_starts_aux_get
  have h2: (F1.P.get! i)∈ F1.P:= by
    sorry
  have hi8:i<F1.k:= by
    exact Nat.lt_of_lt_of_le hi F1k
  exact hi8
  exact ha1
  simp
  exact ha2
  exact hk


  --repeat previous lemmas for E
  sorry

by_contra cont
rw[cont] at hain
have neg: ¬ (Disjoint {v | v ∈ (F2.P.get! j).Pa.Wa.support} {v | (∃ Pi ∈ F1.P, v ∈ Pi.Pa.Wa.support) ∧ v ∉ F1.S ∧ v ∉ F1.E}):= by
  refine Set.not_disjoint_iff.mpr ?_
  use b
exact neg hx



lemma internally_disjoint_symm
(P1 P2: SubgraphPath_implicit G)
(h: internally_disjoint P1 P2)
:
internally_disjoint P2 P1
:= by
unfold internally_disjoint at h
unfold internally_disjoint
rw[Set.inter_comm]
exact h







lemma support_to_interior
(u v : V)
(P: G.Walk u v)
:
{v: V| v ∈ P.support} = interior P∪ {u, v}
:= by
unfold interior
ext x
simp
constructor
intro h
by_cases c1:x=u
left
exact c1
by_cases c2:x=v
right
left
exact c2
right
right
exact ⟨h, c1, c2 ⟩
intro
  a
simp_all only [gt_iff_lt]
unhygienic
    aesop_cases
      a <;>
  [skip;
  (unhygienic
      aesop_cases
        h_1)]
· aesop_subst
    h_1
  simp_all only [Walk.start_mem_support]
· aesop_subst
    h_1
  simp_all only [Walk.end_mem_support]
·
  simp_all only



lemma support_to_interior_tail
{u v : V}
{P: G.Walk u v}
(hneq: u≠ v)
(ispath: P.IsPath)
:
{v: V| v ∈ P.support.tail} = interior P∪ {v}
:= by
unfold interior
ext x
simp
constructor
intro h
by_cases c2:x=v
left
exact c2
right
constructor
have h1: P.support.tail⊆ P.support:= by
  exact List.tail_subset P.support
exact h1 h
constructor
have h2: u∉ P.support.tail:= by
  exact Walk_start_not_in_tail P ispath
exact ne_of_mem_of_not_mem h h2
exact c2
intro y

by_cases hcase: x ∈ P.support
--have h1: x∈ P.support:= by
--  simp_all only [gt_iff_lt,
--    true_and]
rw[Walk.support_eq_cons] at hcase
simp at hcase
rcases hcase with case1|case2
rcases y with case3|case4
rw[case1] at case3
exact (hneq case3).elim
exfalso
exact case4.2.1 case1

exact case2
rcases y with case3|case4
have h1: v∈ P.support:= by
  exact Walk.end_mem_support P
simp_rw[case3.symm] at h1
exact (hcase h1).elim
exfalso
have h4:_:= by
  exact case4.1
exact hcase h4




lemma internal_disjoint_to_tail_disjoint12
(a b c d: V)
(P1 P2 P3: SubgraphPath_implicit G)
(ha: a=P1.s)
(hb: b=P1.e)
(hc: c=P3.s)
(hd: d=P3.e)
(hP1_P2: P1.e=P2.s)
(hP2_P3: P2.e=P3.s)
--(disj_P1_P2: internally_disjoint   P1 P2)
--(disj_P2_P3: internally_disjoint   P2 P3)
--(disj_P1_P3: internally_disjoint   P1 P3)
(ab: a≠ b)(ac: a≠ c)(ad: a≠ d)
(bc: b≠ c)(bd: b≠ d)(cd: c≠ d)
(interiordisj1: Disjoint {a,b,c,d} (interior P1.Pa.Wa))
(interiordisj2: Disjoint {a,b,c,d} (interior P2.Pa.Wa))
(interiordisj3: Disjoint {a,b,c,d} (interior P3.Pa.Wa))
:
tail_disjoint_imp P1 P2
:= by
unfold tail_disjoint_imp
intro v hv1 hv2
--by_cases case : v∈ interior P2.Pa.Wa
have hv1':v∈ {x:V|x∈ P1.Pa.Wa.support}:= by
  simp
  exact hv1
have hv2':v∈ {x:V|x∈ P2.Pa.Wa.support.tail}:= by
  simp
  exact hv2
rw[support_to_interior] at hv1'
rw[support_to_interior_tail _ P2.Pa.Wa_Is_Path ] at hv2'

simp at hv1'
simp at hv2'
rcases hv2' with hv2''|hv2''
rcases hv1' with hv1''|hv1''|hv1''

aesop_subst
  [ha,
  hd,
  hb,
  hv2'',
  hc]
simp_all only [gt_iff_lt]
aesop_subst
  [ha,
  hd,
  hb,
  hv1'',
  hc]
simp_all only [gt_iff_lt,
  ne_eq,
  not_false_eq_true,
  not_true_eq_false]
rw[hP2_P3, hc.symm] at hv2''
rw[hv2'']at hv1''
have neg:¬ (Disjoint {a,b,c,d} (interior P1.Pa.Wa)):= by
  rw [@Set.not_disjoint_iff]
  use v
  constructor
  rw[hv2'']
  simp
  rw[hv2''.symm] at hv1''
  exact hv1''
exact neg interiordisj1

sorry
sorry


--exact fun a ↦ bc rfl


lemma internal_disjoint_to_tail_disjoint13
(a b c d: V)
(P1 P2 P3: SubgraphPath_implicit G)
(ha: a=P1.s)
(hb: b=P1.e)
(hc: c=P3.s)
(hd: d=P3.e)
(hP1_P2: P1.e=P2.s)
(hP2_P3: P2.e=P3.s)
(disj_P1_P2: internally_disjoint   P1 P2)
(disj_P2_P3: internally_disjoint   P2 P3)
(disj_P1_P3: internally_disjoint   P1 P3)
(ab: a≠ b)(ac: a≠ c)(ad: a≠ d)
(bc: b≠ c)(bd: b≠ d)(cd: c≠ d)
(interiordisj1: Disjoint {a,b,c,d} (interior P1.Pa.Wa))
(interiordisj2: Disjoint {a,b,c,d} (interior P2.Pa.Wa))
(interiordisj3: Disjoint {a,b,c,d} (interior P3.Pa.Wa))
:
tail_disjoint_imp P1 P3
:=by
sorry

lemma internal_disjoint_to_tail_disjoint23
(a b c d: V)
(P1 P2 P3: SubgraphPath_implicit G)
(ha: a=P1.s)
(hb: b=P1.e)
(hc: c=P3.s)
(hd: d=P3.e)
(hP1_P2: P1.e=P2.s)
(hP2_P3: P2.e=P3.s)
(disj_P1_P2: internally_disjoint   P1 P2)
(disj_P2_P3: internally_disjoint   P2 P3)
(disj_P1_P3: internally_disjoint   P1 P3)
(ab: a≠ b)(ac: a≠ c)(ad: a≠ d)
(bc: b≠ c)(bd: b≠ d)(cd: c≠ d)
(interiordisj1: Disjoint {a,b,c,d} (interior P1.Pa.Wa))
(interiordisj2: Disjoint {a,b,c,d} (interior P2.Pa.Wa))
(interiordisj3: Disjoint {a,b,c,d} (interior P3.Pa.Wa))
:
tail_disjoint_imp P2 P3
:= by
sorry


lemma join_three_paths_internal_disjoint
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
(disj_P1_P2: internally_disjoint   P1 P2)
(disj_P2_P3: internally_disjoint   P2 P3)
--(disj_P3_P1: tail_disjoint_imp   P3 P1)
(disj_P1_P3: internally_disjoint   P1 P3)
(b c:V)
(hb: b=P1.e)
(hc: c=P3.s)
(ab: a≠ b)(ac: a≠ c)(ad: a≠ d)
(bc: b≠ c)(bd: b≠ d)(cd: c≠ d)
(interiordisj1: Disjoint {a,b,c,d} (interior P1.Pa.Wa))
(interiordisj2: Disjoint {a,b,c,d} (interior P2.Pa.Wa))
(interiordisj3: Disjoint {a,b,c,d} (interior P3.Pa.Wa))

:
∃ (P: SubgraphPath H a d),
P.Wa.support=P1.Pa.Wa.support++P2.Pa.Wa.support.tail++P3.Pa.Wa.support.tail
∧ {v:V|v∈ P.Wa.support}= {v:V|v∈ P1.Pa.Wa.support} ∪ {v:V|v∈ P2.Pa.Wa.support} ∪ {v:V|v∈ P3.Pa.Wa.support}
:= by
apply join_three_paths
repeat assumption
apply internal_disjoint_to_tail_disjoint12 a b c d P1 P2 P3
repeat assumption
apply internal_disjoint_to_tail_disjoint23 a b c d P1 P2 P3
repeat assumption
apply internal_disjoint_to_tail_disjoint13 a b c d P1 P2 P3
repeat assumption















def internally_disjoint_from_set
(P1: SubgraphPath_implicit G)
(S: Set V)
:=
 (interior P1.Pa.Wa)∩  (S)= ∅







lemma join_three_forests_internal_disjoint
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


( hdisj11: ∀(i j: ℕ ), (i< j)→ (j<tmax)→ (internally_disjoint (F1.P.get! i) (F1.P.get! j)))
( hdisj22: ∀(i j: ℕ ), (i< j)→ (j<tmax)→ (internally_disjoint (F2.P.get! i) (F2.P.get! j)))
( hdisj33: ∀(i j: ℕ ), (i< j)→ (j<tmax)→ (internally_disjoint (F3.P.get! i) (F3.P.get! j)))
( hdisj12: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (internally_disjoint (F1.P.get! i) (F2.P.get! j)))
( hdisj21: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (internally_disjoint (F2.P.get! i) (F1.P.get! j)))
( hdisj13: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (internally_disjoint (F1.P.get! i) (F3.P.get! j)))
( hdisj31: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (internally_disjoint (F3.P.get! i) (F1.P.get! j)))
( hdisj23: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (internally_disjoint (F2.P.get! i) (F3.P.get! j)))
( hdisj32: ∀(i j: ℕ ), (i< tmax)→ (i<tmax)→ (internally_disjoint (F3.P.get! i) (F2.P.get! j)))

(Slength: tmax < F1.S.length)

(ht: t<tmax)
(pos1: tmax<F1.k)
(pos2: tmax<F2.k)
(pos3: tmax<F3.k)

(nodupS1: F1.S.Nodup)
(nodupS2: F2.S.Nodup)
(nodupS3: F3.S.Nodup)
(dis12: List.Disjoint F1.S F2.S)
(dis23: List.Disjoint F2.S F3.S)
(dis13: List.Disjoint F1.S F3.S)
(disj1: ∀ (i : ℕ ), (i< tmax)→ (internally_disjoint_from_set (F1.P.get! i) {v:V|v∈ F1.S∪ F2.S∪ F3.S}))
(disj2: ∀ (i : ℕ ), (i< tmax)→ (internally_disjoint_from_set (F2.P.get! i) {v:V|v∈ F1.S∪ F2.S∪ F3.S}))
(disj3: ∀ (i : ℕ ), (i< tmax)→ (internally_disjoint_from_set (F3.P.get! i) {v:V|v∈ F1.S∪ F2.S∪ F3.S}))

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
  apply  join_three_paths_internal_disjoint H (F1.P.get! 0) (F2.P.get! 0) (F3.P.get! 0) (F1.S.get! 0) (F3.E.get! (0))
  apply  F1.Graphs_equal 0 pos1
  apply  F2.Graphs_equal 0 pos2
  apply  F3.Graphs_equal 0 pos3

  apply F1.Starts_equal
  exact pos1

  rw [F3.Ends_equal 0 pos3]


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
  apply hdisj13; exact ht; exact ht

  have h1: (F1.P.get! 0).e=(F1.P.get! 0).e:= by exact rfl
  exact h1
  have h1: (F3.P.get! 0).s=(F3.P.get! 0).s:= by exact rfl
  exact h1
  sorry
  sorry
  sorry
  sorry
  sorry
  sorry

  sorry
  sorry
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


have hdisj11: ∀(i j: ℕ ), (i< j)→ (j<t+2)→ (internally_disjoint (F1.P.get! i) (F1.P.get! j)):= by
  intro i j hi hj;  apply hdisj11; exact hi; exact Nat.lt_of_lt_of_le hj ht

have hdisj22: ∀(i j: ℕ ), (i< j)→ (j<t+2)→ (internally_disjoint (F2.P.get! i) (F2.P.get! j)):= by
  intro i j hi hj;  apply hdisj22; exact hi; exact Nat.lt_of_lt_of_le hj ht
have hdisj33: ∀(i j: ℕ ), (i< j)→ (j<t+2)→ (internally_disjoint (F3.P.get! i) (F3.P.get! j)):= by
  intro i j hi hj;  apply hdisj33; exact hi; exact Nat.lt_of_lt_of_le hj ht

have hdisj12: ∀(i j: ℕ ), (i< t+2)→ (i<t+2)→ (internally_disjoint (F1.P.get! i) (F2.P.get! j)):= by
  intro i j hi hj;  apply hdisj12; exact Nat.lt_of_lt_of_le hi ht; exact Nat.lt_of_lt_of_le hj ht
have hdisj21: ∀(i j: ℕ ), (i< t+2)→ (i<t+2)→ (internally_disjoint (F2.P.get! i) (F1.P.get! j)):= by
  intro i j hi hj;  apply hdisj21; exact Nat.lt_of_lt_of_le hi ht; exact Nat.lt_of_lt_of_le hj ht
have hdisj13: ∀(i j: ℕ ), (i< t+2)→ (i<t+2)→ (internally_disjoint (F1.P.get! i) (F3.P.get! j)):= by
  intro i j hi hj;  apply hdisj13; exact Nat.lt_of_lt_of_le hi ht; exact Nat.lt_of_lt_of_le hj ht
have hdisj31: ∀(i j: ℕ ), (i< t+2)→ (i<t+2)→ (internally_disjoint (F3.P.get! i) (F1.P.get! j)):= by
  intro i j hi hj;  apply hdisj31; exact Nat.lt_of_lt_of_le hi ht; exact Nat.lt_of_lt_of_le hj ht
have hdisj23: ∀(i j: ℕ ), (i< t+2)→ (i<t+2)→ (internally_disjoint (F2.P.get! i) (F3.P.get! j)):= by
  intro i j hi hj;  apply hdisj23; exact Nat.lt_of_lt_of_le hi ht; exact Nat.lt_of_lt_of_le hj ht
have hdisj32: ∀(i j: ℕ ), (i< t+2)→ (i<t+2)→ (internally_disjoint (F3.P.get! i) (F2.P.get! j)):= by
  intro i j hi hj;  apply hdisj32; exact Nat.lt_of_lt_of_le hi ht; exact Nat.lt_of_lt_of_le hj ht



have pos1: t+1<F1.k:= by exact Nat.lt_trans ht pos1
have pos2: t+1<F2.k:= by exact Nat.lt_trans ht pos2
have pos3: t+1<F3.k:= by exact Nat.lt_trans ht pos3

have hex: _:= by
  apply  join_three_paths_internal_disjoint H (F1.P.get! (t+1)) (F2.P.get! (t+1)) (F3.P.get! (t+1)) (F3.E.get! t) (F3.E.get! ((t+1)))
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

  sorry
  sorry

  sorry
  sorry
  sorry
  sorry
  sorry
  sorry

  sorry
  sorry
  sorry
  sorry
  


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
  apply hdisj21 i (t+1); exact Nat.lt_succ_of_lt hi1; exact Nat.lt_succ_of_lt hi1; exact hi2

  unfold Path_forest_support_until_t at c2
  simp at c2
  rcases c2 with ⟨ i, ⟨ hi1, hi2⟩ ⟩
  apply hdisj31 i (t+1); exact Nat.lt_succ_of_lt hi1; exact Nat.lt_succ_of_lt hi1; exact hi2


  constructor
  rcases hp1 with c1|c1
  rcases c1 with c1|c1

  unfold Path_forest_support_until_t at c1
  simp at c1
  rcases c1 with ⟨ i, ⟨ hi1, hi2⟩ ⟩
  apply hdisj12 i (t+1); exact Nat.lt_succ_of_lt hi1; exact Nat.lt_succ_of_lt hi1; exact hi2

  unfold Path_forest_support_until_t at c1
  simp at c1
  rcases c1 with ⟨ i, ⟨ hi1, hi2⟩ ⟩
  apply hdisj22 i (t+1); exact hi1; exact Nat.lt.base (t + 1); exact hi2

  unfold Path_forest_support_until_t at c1
  simp at c1
  rcases c1 with ⟨ i, ⟨ hi1, hi2⟩ ⟩
  apply hdisj32 i (t+1); exact Nat.lt_succ_of_lt hi1; exact Nat.lt_succ_of_lt hi1; exact hi2

  rcases hp1 with c1|c1
  rcases c1 with c1|c1

  unfold Path_forest_support_until_t at c1
  simp at c1
  rcases c1 with ⟨ i, ⟨ hi1, hi2⟩ ⟩
  apply hdisj13 i (t+1); exact Nat.lt_succ_of_lt hi1; exact Nat.lt_succ_of_lt hi1; exact hi2

  unfold Path_forest_support_until_t at c1
  simp at c1
  rcases c1 with ⟨ i, ⟨ hi1, hi2⟩ ⟩
  apply hdisj23 i (t+1); exact Nat.lt_succ_of_lt hi1; exact Nat.lt_succ_of_lt hi1; exact hi2

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
sorry
