import MyProject

import MyProject.path_forests_clump_sequence_preparation
--C:\Users\alja1\Downloads\pro\my_project\MyProject\path_forests_clump_sequence_preparation.lean
open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats    50000

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
(F1_in_Fb: {v:V| v∈ Path_forest_support iV iSP F1∧ v∉ F2.S}= Fb)
(hk: F1.k=F1.S.length)
:
∀(i j: ℕ ), (i< k)→ (j<k)→ (tail_disjoint_imp (F1.P.get! i) (F2.P.get! j))
:= by

intro i j hi hj
unfold tail_disjoint_imp
intro a ha hb

--unfold interior
--intro a ha
--intro b hb
--simp at ha
--simp at hb
rw[Walk.support_eq_cons (F1.P.get! i).Pa.Wa] at ha
simp at ha

--let ⟨ha1, ha2, ha3⟩:=ha
--let ⟨hb1, hb2, hb3⟩:=hb
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
