import MyProject

import MyProject.path_forests_clump_sequence_preparation
--C:\Users\alja1\Downloads\pro\my_project\MyProject\path_forests_clump_sequence_preparation.lean
open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats    150000

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

lemma path_implicit_tail_s_append
(P: SubgraphPath_implicit G)
:
P.Pa.Wa.support=[P.s]++P.Pa.Wa.support.tail
:= by
rw [@List.singleton_append]
rw [← @Walk.support_eq_cons]

lemma start_not_in_tail
(P: SubgraphPath_implicit G)
:
P.s∉ P.Pa.Wa.support.tail
:= by
refine Walk_start_not_in_tail P.Pa.Wa ?hP
exact P.Pa.Wa_Is_Path

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



lemma Path_forest_get_start
(F: PathForest iV iSP H)
(i: ℕ )
(hi: i< F.k)
(v: V)
(hv: v ∈ (F.P.get! i).Pa.Wa.support)
(inStarts: v∈  F.S)
--(hv2: v≠ (F.P.get! i).s)
(hk: F.k=F.S.length)
:
v= (F.P.get! i).s
:= by
by_contra cont
have hc: v∉  F.S:= by
  exact Path_forest_starts_aux_get iV iSP F i hi v hv cont hk
exact hc inStarts


lemma Path_forest_get_start2
(F: PathForest iV iSP H)
(i: ℕ )
(hi: i< F.k)
(v: V)
(hv: v ∈ (F.P.get! i).Pa.Wa.support)
(inStarts: v∈  F.S)
--(hv2: v≠ (F.P.get! i).s)
(hk: F.k=F.S.length)
:
v= (F.S.get! i)
:= by
rw[F.Starts_equal i hi]
exact Path_forest_get_start iV iSP F i hi v hv inStarts hk



lemma Path_forest_get_end2
(F: PathForest iV iSP H)
(i: ℕ )
(hi: i< F.k)
(v: V)
(hv: v ∈ (F.P.get! i).Pa.Wa.support)
(inStarts: v∈  F.E)
--(hv2: v≠ (F.P.get! i).s)
(hk: F.k=F.E.length)
:
v= (F.E.get! i)
:= by
sorry

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




lemma set_disjoint_to_tail_disjoint_forward
(F1  F2: PathForest iV iSP H)
(Fb: Set V)
(k: ℕ )
(F1k: F1.k≥ k)
(F2k: F2.k≥ k)
(F2k2: F2.k = F2.S.length)
(F2_avoids_Fb: Path_forest_avoids! iV iSP F2 Fb k)
(F1_in_Fb: {v:V| v∈ Path_forest_support iV iSP F1∧ v∉ F2.S}= Fb)
(hk: F1.k=F1.S.length)
:
∀(i j: ℕ ), (i< k)→ (j<k)→ (tail_disjoint_imp (F1.P.get! i) (F2.P.get! j))
:= by

intro i j hi hj
unfold tail_disjoint_imp
apply List.disjoint_left.mpr-- List.Disjoint.symm ((fun {α} {l₁ l₂} ↦ List.disjoint_left.mpr) ?_)
intro a ha
unfold Path_forest_avoids! at F2_avoids_Fb
rw [F1_in_Fb.symm] at F2_avoids_Fb
by_contra cont

have hF2: a∈ {v | v ∈ (F2.P.get! j).Pa.Wa.support}:= by
  have h2: a∈ {v | v ∈ (F2.P.get! j).Pa.Wa.support.tail}:= by
    simp
    exact cont
  have h3: {v | v ∈ (F2.P.get! j).Pa.Wa.support.tail}⊆ {v | v ∈ (F2.P.get! j).Pa.Wa.support}:= by
    simp
    exact fun a a_1 ↦ List.mem_of_mem_tail a_1
  exact h3 cont


have geti: (F1.P.get! i)= (F1.P.get ⟨ i, _⟩ ):= by
  simp
  refine List.getD_eq_get F1.P default ?_
  calc
    i<k:= by exact hi
    _≤ F1.k:= by exact F1k
    _= F1.P.length:= by exact F1.P_length.symm
have hF1: a∉ {v | v ∈ Path_forest_support iV iSP F1 ∧ v ∉ F2.S}:= by
  by_contra cont2
  have h1: ¬( ∀ (i: ℕ ), i < k→  Disjoint {v | v ∈ (F2.P.get! i).Pa.Wa.support} {v | v ∈ Path_forest_support iV iSP F1 ∧ v ∉ F2.S}):= by
    push_neg
    use j
    constructor
    exact hj
    rw [@Set.not_disjoint_iff]
    use a
  exact h1 F2_avoids_Fb
simp only [Set.mem_setOf_eq, not_and, Decidable.not_not] at hF1
have InSup: a ∈ Path_forest_support iV iSP F1:= by
  unfold Path_forest_support
  simp
  use (F1.P.get! i)
  constructor
  rw[geti]
  exact List.get_mem F1.P i (Trans.trans (Trans.trans hi F1k) F1.P_length.symm)
  exact ha
have inS: a ∈ F2.S:= by
  exact hF1 InSup

have ninS: a ∉ F2.S:=by
  apply Path_forest_starts_aux_get
  have hjl: j<F2.k:= by
    calc
      j<k:= by exact hj
      _≤ F2.k:= by exact F2k
  exact hjl
  --have sublis: (F2.P.get! j).Pa.Wa.support.tail⊆  (F2.P.get! j).Pa.Wa.support:= by
  --  exact List.tail_subset (F2.P.get! j).Pa.Wa.support
  exact hF2
  by_contra cont3
  rw[cont3] at cont
  have h4: (F2.P.get! j).s ∉  (F2.P.get! j).Pa.Wa.support.tail:= by
    exact start_not_in_tail (F2.P.get! j)
  exact h4 cont
  exact F2k2
exact ninS (hF1 InSup)




lemma set_disjoint_to_internal_disjoint_reverse
(F1  F2: PathForest iV iSP H)
(Fb: Set V)
(k: ℕ )
(F1k: F1.k≥ k)
(F2k: F2.k≥ k)
(F2k2: F2.k = F2.S.length)
(F1k2: F1.k = F1.E.length)
(Ends_eq:F1.E=F2.S)
(F2SNodup: F2.S.Nodup)
(F2_avoids_Fb: Path_forest_avoids! iV iSP F2 Fb k)
(F1_in_Fb: {v:V| v∈ Path_forest_support iV iSP F1∧ v∉ F2.S}= Fb)
(hk: F1.k=F1.S.length)
:
∀(i j: ℕ ), (i< k)→ (j<i)→  (List.Disjoint (F2.P.get! i).Pa.Wa.support (F1.P.get! j).Pa.Wa.support)
:= by
intro i j hi hj2
have hj: j<k:= by
  calc
    j<i:= by exact hj2
    _< k:= by exact hi
unfold Path_forest_avoids! at F2_avoids_Fb
rw [F1_in_Fb.symm] at F2_avoids_Fb
refine List.disjoint_left.mpr ?_
intro a ha

by_contra cont0

have hF1: a∉ {v | v ∈ Path_forest_support iV iSP F1 ∧ v ∉ F2.S}:= by
  by_contra cont2
  have h1: ¬( ∀ (i: ℕ ), i < k→  Disjoint {v | v ∈ (F2.P.get! i).Pa.Wa.support} {v | v ∈ Path_forest_support iV iSP F1 ∧ v ∉ F2.S}):= by
    push_neg
    use i
    constructor
    exact hi
    rw [@Set.not_disjoint_iff]
    use a
    constructor
    exact ha
    simp at cont2
    simp
    exact cont2

  exact h1 F2_avoids_Fb
simp at hF1
have nin: a∉ F2.S:= by
  by_contra cont
  have h1:a=F2.S.get! i:= by
    apply Path_forest_get_start2
    calc
      i<k:= by exact hi
      _≤ F2.k:= by exact F2k
    exact ha
    exact cont
    exact F2k2
  have h2:a=F1.E.get! j:= by
    rw [Ends_eq.symm] at cont
    apply Path_forest_get_end2
    calc
      j<k:= by exact hj
      _≤ F1.k:= by exact F1k
    exact cont0
    exact cont
    exact F1k2
  rw [Ends_eq, h1] at h2
  have dup: ¬ (F2.S.Nodup):= by
    rw [← @List.exists_duplicate_iff_not_nodup]
    use F2.S.get! i
    refine List.duplicate_iff_exists_distinct_get.mpr ?h.a

    use ⟨ j, ?_⟩
    use ⟨  i, ?_⟩
    simp only [exists_and_left, exists_prop]
    constructor
    rw[h2]
    simp
    apply List.getD_eq_get
    calc
      j<k:= by exact hj
      _≤ F2.k:= by exact F2k
      _=F2.S.length:= by exact F2k2
    constructor
    exact hj2
    simp
    apply List.getD_eq_get
    calc
      i<k:= by exact hi
      _≤ F2.k:= by exact F2k
      _=F2.S.length:= by exact F2k2
  have nodup: F2.S.Nodup:= by
    exact F2SNodup
  exact dup F2SNodup
have inn: a∈ F2.S:= by
  apply hF1
  unfold Path_forest_support
  simp
  use  (F1.P.get! j)
  constructor
  have h3: F1.P.get! j =F1.P.get ⟨ j, _⟩:= by
    simp
    refine List.getD_eq_get F1.P default ?_
    calc
      j<k:= by exact hj
      _≤ F1.k:= by exact F1k
      _=F1.P.length:= by exact F1.P_length.symm
  rw[h3]
  exact List.get_mem F1.P j (Trans.trans (Trans.trans hj F1k) F1.P_length.symm)
  exact cont0
exact nin inn





lemma set_disjoint_to_internal_disjoint_reverse2
(F1  F2: PathForest iV iSP H)
(Fb: Set V)
(k: ℕ )
(F1k: F1.k≥ k)
(F2k: F2.k≥ k)
(F2k2: F2.k = F2.S.length)
(F1k2: F1.k = F1.E.length)
(Ends_eq:F1.E=F2.S)
(F2SNodup: F2.S.Nodup)
(F2_avoids_Fb: Path_forest_avoids! iV iSP F2 Fb k)
(F1_in_Fb: {v:V| v∈ Path_forest_support iV iSP F1∧ v∉ F2.S}= Fb)
(hk: F1.k=F1.S.length)
:
∀(i j: ℕ ), (j< k)→ (i<j)→  (List.Disjoint (F2.P.get! i).Pa.Wa.support (F1.P.get! j).Pa.Wa.support)
:= by
intro i j hj hj2
have hi: i<k:= by
  calc
    i<j:= by exact hj2
    _< k:= by exact hj
unfold Path_forest_avoids! at F2_avoids_Fb
rw [F1_in_Fb.symm] at F2_avoids_Fb
refine List.disjoint_left.mpr ?_
intro a ha

by_contra cont0

have hF1: a∉ {v | v ∈ Path_forest_support iV iSP F1 ∧ v ∉ F2.S}:= by
  by_contra cont2
  have h1: ¬( ∀ (i: ℕ ), i < k→  Disjoint {v | v ∈ (F2.P.get! i).Pa.Wa.support} {v | v ∈ Path_forest_support iV iSP F1 ∧ v ∉ F2.S}):= by
    push_neg
    use i
    constructor
    exact hi
    rw [@Set.not_disjoint_iff]
    use a
    constructor
    exact ha
    simp at cont2
    simp
    exact cont2

  exact h1 F2_avoids_Fb
simp at hF1
have nin: a∉ F2.S:= by
  by_contra cont
  have h1:a=F2.S.get! i:= by
    apply Path_forest_get_start2
    calc
      i<k:= by exact hi
      _≤ F2.k:= by exact F2k
    exact ha
    exact cont
    exact F2k2
  have h2:a=F1.E.get! j:= by
    rw [Ends_eq.symm] at cont
    apply Path_forest_get_end2
    calc
      j<k:= by exact hj
      _≤ F1.k:= by exact F1k
    exact cont0
    exact cont
    exact F1k2
  rw [Ends_eq, h1] at h2
  have dup: ¬ (F2.S.Nodup):= by
    rw [← @List.exists_duplicate_iff_not_nodup]
    use F2.S.get! i
    refine List.duplicate_iff_exists_distinct_get.mpr ?h.a

    use ⟨ i, ?_⟩
    use ⟨  j, ?_⟩
    simp only [exists_and_left, exists_prop]
    constructor



    simp
    apply List.getD_eq_get
    constructor
    exact hj2
    rw[h2]
    simp
    apply List.getD_eq_get
    calc
      j<k:= by exact hj
      _≤ F2.k:= by exact F2k
      _=F2.S.length:= by exact F2k2

    calc
      i<k:= by exact hi
      _≤ F2.k:= by exact F2k
      _=F2.S.length:= by exact F2k2
  have nodup: F2.S.Nodup:= by
    exact F2SNodup
  exact dup F2SNodup
have inn: a∈ F2.S:= by
  apply hF1
  unfold Path_forest_support
  simp
  use  (F1.P.get! j)
  constructor
  have h3: F1.P.get! j =F1.P.get ⟨ j, _⟩:= by
    simp
    refine List.getD_eq_get F1.P default ?_
    calc
      j<k:= by exact hj
      _≤ F1.k:= by exact F1k
      _=F1.P.length:= by exact F1.P_length.symm
  rw[h3]
  exact List.get_mem F1.P j (Trans.trans (Trans.trans hj F1k) F1.P_length.symm)
  exact cont0
exact nin inn











lemma Fb_disj_symm
(F1  F2: PathForest iV iSP H)
(k: ℕ )
(F1k: F1.k= k)
(F2k: F2.k= k)
(Fb1: Set V)
(Fb2: Set V)
(Ends_equal: F1.E=F2.S)
(F2_avoids_Fb: Path_forest_avoids! iV iSP F2 Fb1 k)
(Fb1Def: {v:V| v∈ Path_forest_support iV iSP F1∧ v∉ F2.S}= Fb1)
(Fb2Def: {v:V| v∈ Path_forest_support iV iSP F2∧ v∉ F1.E}= Fb2)
:
Path_forest_avoids! iV iSP F1 Fb2 k
:= by
unfold Path_forest_avoids!
rw[Fb2Def.symm]
intro i hi

rw [@Set.disjoint_left]
intro a ha
simp
simp only [Set.mem_setOf_eq] at ha
intro ha2
unfold Path_forest_avoids! at F2_avoids_Fb
unfold Path_forest_support at ha2

simp at ha2
rcases ha2 with ⟨P2, hP2a, hP2b⟩
have jex: ∃ (j: Fin (F2.P.length) ),  F2.P.get j=P2:= by
  apply List.mem_iff_get.1
  exact hP2a
rcases jex with ⟨j, hj⟩
have jget: F2.P.get j =F2.P.get! j:= by
  simp
  symm
  apply List.getD_eq_get

have hdis: Disjoint {v | v ∈ (F2.P.get! j).Pa.Wa.support} Fb1:= by
  apply F2_avoids_Fb
  calc
    _ < F2.P.length:= by exact j.isLt
    _= F2.k:= by exact F2.P_length
    _= k:= by exact F2k

have hain: a∈ {v | v ∈ (F2.P.get! ↑j).Pa.Wa.support} :=by
  simp
  rw[jget.symm]
  rw[hj]
  exact hP2b
have anin: a∉ Fb1:= by
  refine Set.disjoint_singleton_left.mp ?_
  apply Set.disjoint_of_subset_left
  simp
  exact hain
  exact hdis
rw [Fb1Def.symm] at anin
simp at anin
rw[Ends_equal]
apply anin
unfold Path_forest_support
simp
use F1.P.get! i
constructor
have h6:F1.P.get! i=F1.P.get ⟨ i, _⟩:= by
  simp
  refine List.getD_eq_get F1.P default ?_
  calc
    i<k:= by exact hi
    _= F1.k:= by exact F1k.symm
    _=F1.P.length:= by exact F1.P_length.symm
rw[h6]
exact List.get_mem F1.P i (Trans.trans (Trans.trans hi F1k.symm) F1.P_length.symm)
exact ha




lemma Fb_disj_symm2
(F1  F2: PathForest iV iSP H)
(k: ℕ )
(F1k: F1.k= k)
(F2k: F2.k= k)
(Fb1: Set V)
(Fb2: Set V)
(Ends_equal: F1.S=F2.E)
(F2_avoids_Fb: Path_forest_avoids! iV iSP F2 Fb1 k)
(Fb1Def: {v:V| v∈ Path_forest_support iV iSP F1∧ v∉ F2.E}= Fb1)
(Fb2Def: {v:V| v∈ Path_forest_support iV iSP F2∧ v∉ F1.S}= Fb2)
:
Path_forest_avoids! iV iSP F1 Fb2 k
:= by
unfold Path_forest_avoids!
rw[Fb2Def.symm]
intro i hi

rw [@Set.disjoint_left]
intro a ha
simp
simp only [Set.mem_setOf_eq] at ha
intro ha2
unfold Path_forest_avoids! at F2_avoids_Fb
unfold Path_forest_support at ha2

simp at ha2
rcases ha2 with ⟨P2, hP2a, hP2b⟩
have jex: ∃ (j: Fin (F2.P.length) ),  F2.P.get j=P2:= by
  apply List.mem_iff_get.1
  exact hP2a
rcases jex with ⟨j, hj⟩
have jget: F2.P.get j =F2.P.get! j:= by
  simp
  symm
  apply List.getD_eq_get

have hdis: Disjoint {v | v ∈ (F2.P.get! j).Pa.Wa.support} Fb1:= by
  apply F2_avoids_Fb
  calc
    _ < F2.P.length:= by exact j.isLt
    _= F2.k:= by exact F2.P_length
    _= k:= by exact F2k

have hain: a∈ {v | v ∈ (F2.P.get! ↑j).Pa.Wa.support} :=by
  simp
  rw[jget.symm]
  rw[hj]
  exact hP2b
have anin: a∉ Fb1:= by
  refine Set.disjoint_singleton_left.mp ?_
  apply Set.disjoint_of_subset_left
  simp
  exact hain
  exact hdis
rw [Fb1Def.symm] at anin
simp at anin
rw[Ends_equal]
apply anin
unfold Path_forest_support
simp
use F1.P.get! i
constructor
have h6:F1.P.get! i=F1.P.get ⟨ i, _⟩:= by
  simp
  refine List.getD_eq_get F1.P default ?_
  calc
    i<k:= by exact hi
    _= F1.k:= by exact F1k.symm
    _=F1.P.length:= by exact F1.P_length.symm
rw[h6]
exact List.get_mem F1.P i (Trans.trans (Trans.trans hi F1k.symm) F1.P_length.symm)
exact ha


lemma set_disjoint_to_internal_disjoint_reverse_neq
(F1  F2: PathForest iV iSP H)
(Fb: Set V)
(k: ℕ )
(F1k: F1.k≥ k)
(F2k: F2.k≥ k)
(F2k2: F2.k = F2.S.length)
(F1k2: F1.k = F1.E.length)
(Ends_eq:F1.E=F2.S)
(F2SNodup: F2.S.Nodup)
(F2_avoids_Fb: Path_forest_avoids! iV iSP F2 Fb k)
(F1_in_Fb: {v:V| v∈ Path_forest_support iV iSP F1∧ v∉ F2.S}= Fb)
(hk: F1.k=F1.S.length)
:
∀(i j: ℕ ), (i< k)→ (j<k)→ i≠ j→  (List.Disjoint (F2.P.get! i).Pa.Wa.support (F1.P.get! j).Pa.Wa.support)
:= by
intro i j hi hj hneq
by_cases case: j<i
apply set_disjoint_to_internal_disjoint_reverse
exact F1k
repeat assumption

simp at case
have hl: i<j:= by exact Nat.lt_of_le_of_ne case hneq
apply set_disjoint_to_internal_disjoint_reverse2
exact F1k
repeat assumption




lemma set_disjoint_to_internal_disjoint_reverse_taildisj
(F1  F2: PathForest iV iSP H)
(Fb: Set V)
(k: ℕ )
(F1k: F1.k≥ k)
(F2k: F2.k≥ k)
(F2k2: F2.k = F2.S.length)
(F1k2: F1.k = F1.E.length)
(Ends_eq:F1.E=F2.S)
(F2SNodup: F2.S.Nodup)
(F2_avoids_Fb: Path_forest_avoids! iV iSP F2 Fb k)
(F1_in_Fb: {v:V| v∈ Path_forest_support iV iSP F1∧ v∉ F2.S}= Fb)
(hk: F1.k=F1.S.length)
:
∀(i j: ℕ ), (i< k)→ (j<k)→ i≠ j→  (tail_disjoint_imp (F1.P.get! i) (F2.P.get! j))
:= by
intro i j hi hj hneq
unfold tail_disjoint_imp
have h1: (F1.P.get! i).Pa.Wa.support.Disjoint (F2.P.get! j).Pa.Wa.support:= by
  rw [@List.disjoint_comm]
  apply set_disjoint_to_internal_disjoint_reverse_neq
  exact F1k
  exact F2k
  repeat assumption
  exact id (Ne.symm hneq)


have h2: (F2.P.get! j).Pa.Wa.support.tail⊆(F2.P.get! j).Pa.Wa.support:= by
  exact List.tail_subset (F2.P.get! j).Pa.Wa.support
exact  List.Disjoint.symm    ((fun {α} {l₁ l₂} ↦ List.disjoint_left.mpr) fun ⦃a⦄ a_1 ↦ id (List.Disjoint.symm h1) (h2 a_1))




lemma set_disjoint_to_internal_disjoint_reverse_taildisj_symm
(F1  F2: PathForest iV iSP H)
(Fb: Set V)
(k: ℕ )
(F1k: F1.k≥ k)
(F2k: F2.k≥ k)
(F2k2: F2.k = F2.S.length)
(F1k2: F1.k = F1.E.length)
(Ends_eq:F1.E=F2.S)
(F2SNodup: F2.S.Nodup)
(F2_avoids_Fb: Path_forest_avoids! iV iSP F2 Fb k)
(F1_in_Fb: {v:V| v∈ Path_forest_support iV iSP F1∧ v∉ F2.S}= Fb)
(hk: F1.k=F1.S.length)
:
∀(i j: ℕ ), (i< k)→ (j<k)→ i≠ j→  (tail_disjoint_imp  (F2.P.get! j) (F1.P.get! i))
:= by
intro i j hi hj hneq
unfold tail_disjoint_imp
have h1: (F2.P.get! j).Pa.Wa.support.Disjoint (F1.P.get! i).Pa.Wa.support:= by
  --rw [@List.disjoint_comm]
  apply set_disjoint_to_internal_disjoint_reverse_neq
  exact F1k
  exact F2k
  repeat assumption
  exact id (Ne.symm hneq)


have h2: (F1.P.get! i).Pa.Wa.support.tail⊆(F1.P.get! i).Pa.Wa.support:= by
  exact List.tail_subset (F1.P.get! i).Pa.Wa.support
exact  List.Disjoint.symm    ((fun {α} {l₁ l₂} ↦ List.disjoint_left.mpr) fun ⦃a⦄ a_1 ↦ id (List.Disjoint.symm h1) (h2 a_1))




lemma set_disjoint_to_internal_disjoint_reverse_taildisj_symm2
(F1  F2: PathForest iV iSP H)
(Fb: Set V)
(k: ℕ )
(F1k: F1.k≥ k)
(F2k: F2.k≥ k)
(F2k2: F2.k = F2.S.length)
(F1k2: F1.k = F1.E.length)
(Ends_eq:F1.E=F2.S)
(F2SNodup: F2.S.Nodup)
(F2_avoids_Fb: Path_forest_avoids! iV iSP F2 Fb k)
(F1_in_Fb: {v:V| v∈ Path_forest_support iV iSP F1∧ v∉ F2.S}= Fb)
(hk: F1.k=F1.S.length)
:
∀(j i: ℕ ), (j< k)→ (i<k)→ j≠ i→  (tail_disjoint_imp  (F2.P.get! j) (F1.P.get! i))
:= by
intro j i hj hi hneq
apply set_disjoint_to_internal_disjoint_reverse_taildisj_symm
repeat assumption
exact id (Ne.symm hneq)





















lemma set_disjoint_to_internal_disjoint_reverse_tailalign
(F1  F2: PathForest iV iSP H)
(Fb: Set V)
(k: ℕ )
(F1k: F1.k≥ k)
(F2k: F2.k≥ k)
(F2k2: F2.k = F2.S.length)
(F1k2: F1.k = F1.E.length)
(Ends_eq:F1.E=F2.S.tail)
(F2SNodup: F2.S.Nodup)
(F2_avoids_Fb: Path_forest_avoids! iV iSP F2 Fb k)
(F1_in_Fb: {v:V| v∈ Path_forest_support iV iSP F1∧ v∉ F2.S}= Fb)
(hk: F1.k=F1.S.length)
:
∀(i j: ℕ ), (i< k)→ (j<i+1)→  (List.Disjoint (F2.P.get! i).Pa.Wa.support (F1.P.get! j).Pa.Wa.support)
:= by
intro i j hi hj2
have hj: j<k:= by
  sorry
unfold Path_forest_avoids! at F2_avoids_Fb
rw [F1_in_Fb.symm] at F2_avoids_Fb
refine List.disjoint_left.mpr ?_
intro a ha

by_contra cont0

have hF1: a∉ {v | v ∈ Path_forest_support iV iSP F1 ∧ v ∉ F2.S}:= by
  by_contra cont2
  have h1: ¬( ∀ (i: ℕ ), i < k→  Disjoint {v | v ∈ (F2.P.get! i).Pa.Wa.support} {v | v ∈ Path_forest_support iV iSP F1 ∧ v ∉ F2.S}):= by
    push_neg
    use i
    constructor
    exact hi
    rw [@Set.not_disjoint_iff]
    use a
    constructor
    exact ha
    simp at cont2
    simp
    exact cont2

  exact h1 F2_avoids_Fb
simp at hF1
have nin: a∉ F2.S:= by
  by_contra cont
  have h1:a=F2.S.get! i:= by
    apply Path_forest_get_start2
    calc
      i<k:= by exact hi
      _≤ F2.k:= by exact F2k
    exact ha
    exact cont
    exact F2k2
  have h2:a=F1.E.get! j:= by
    rw [Ends_eq.symm] at cont
    apply Path_forest_get_end2
    calc
      j<k:= by exact hj
      _≤ F1.k:= by exact F1k
    exact cont0
    exact cont
    exact F1k2
  rw [Ends_eq, h1] at h2
  have dup: ¬ (F2.S.Nodup):= by
    rw [← @List.exists_duplicate_iff_not_nodup]
    use F2.S.get! i
    refine List.duplicate_iff_exists_distinct_get.mpr ?h.a

    use ⟨ j, ?_⟩
    use ⟨  i, ?_⟩
    simp only [exists_and_left, exists_prop]
    constructor
    rw[h2]
    simp
    apply List.getD_eq_get
    calc
      j<k:= by exact hj
      _≤ F2.k:= by exact F2k
      _=F2.S.length:= by exact F2k2
    constructor
    exact hj2
    simp
    apply List.getD_eq_get
    calc
      i<k:= by exact hi
      _≤ F2.k:= by exact F2k
      _=F2.S.length:= by exact F2k2
  have nodup: F2.S.Nodup:= by
    exact F2SNodup
  exact dup F2SNodup
have inn: a∈ F2.S:= by
  apply hF1
  unfold Path_forest_support
  simp
  use  (F1.P.get! j)
  constructor
  have h3: F1.P.get! j =F1.P.get ⟨ j, _⟩:= by
    simp
    refine List.getD_eq_get F1.P default ?_
    calc
      j<k:= by exact hj
      _≤ F1.k:= by exact F1k
      _=F1.P.length:= by exact F1.P_length.symm
  rw[h3]
  exact List.get_mem F1.P j (Trans.trans (Trans.trans hj F1k) F1.P_length.symm)
  exact cont0
exact nin inn


--simp at ha

/-intro a ha hb

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
-/
