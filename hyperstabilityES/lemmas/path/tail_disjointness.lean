--import MyProject

import hyperstabilityES.lemmas.path.find_path_forest
import hyperstabilityES.lemmas.path.path_forests_join
--C:\Users\alja1\Downloads\pro\my_project\MyProject\path_forests_clump_sequence_preparation.lean
set_option linter.unusedVariables false

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats    250000

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




--used
/-
lemma start_not_in_tail
(P: SubgraphPath_implicit G)
:
P.s∉ P.Pa.Wa.support.tail
:= by
refine Walk_start_not_in_tail P.Pa.Wa ?hP
exact P.Pa.Wa_Is_Path
-/

lemma Path_forest_ends_inter
(F: PathForest iV iSP H)
--(P: SubgraphPath_implicit G)
(i: ℕ )
(hi: i< F.k)
--(v: V)
--(hv: v ∈ P.Pa.Wa.support)
--(hk: F.k=F.E.length)
:
F.E.get! i∈ (F.P.get! i).Pa.Wa.support
:= by
have h1:  (F.P.get! i).e=F.E.get! i:= by
  symm
  exact F.Ends_equal i hi
rw[h1.symm]
exact Walk.end_mem_support (F.P.get! i).Pa.Wa

--not used?
lemma Path_forest_endss_inter2
(F: PathForest iV iSP H)
--(P: SubgraphPath_implicit G)
(i j: ℕ )
(hi: i< F.k)
(hj: j< F.k)
(hij: i< j)
--(v: V)
--(hv: v ∈ P.Pa.Wa.support)
(hk: F.k=F.E.length)
:
F.E.get! j∉  (F.P.get! i).Pa.Wa.support
:= by
by_contra cont
have hhi:  F.E.get! j∈  (F.P.get! j).Pa.Wa.support:= by
  apply Path_forest_ends_inter
  exact hj

have hdisj: _:= by exact F.Paths_disjoint
unfold paths_disjoint at hdisj

have hdisj2: _:= by exact hdisj i j hij hj
have neg: ¬ (Disjoint {v | v ∈ (F.P.get! i).Pa.Wa.support} {v | v ∈ (F.P.get! j).Pa.Wa.support})
:= by
  refine Set.not_disjoint_iff.mpr ?_
  use F.E.get! j
  constructor
  simp only [Set.mem_setOf_eq]
  exact cont

  simp only [Set.mem_setOf_eq]
  exact hhi
exact neg (hdisj i j hij hj)





lemma Path_forest_ends_inter3
(F: PathForest iV iSP H)
--(P: SubgraphPath_implicit G)
(i j: ℕ )
(hi: i< F.k)
(hj: j< F.k)
(hij: i≠  j)
--(v: V)
--(hv: v ∈ P.Pa.Wa.support)
--(hk: F.k=F.S.length)
:
F.E.get! j∉  (F.P.get! i).Pa.Wa.support
:= by
by_contra cont
have hhi:  F.E.get! j∈  (F.P.get! j).Pa.Wa.support:= by
   apply Path_forest_ends_inter
   exact hj


have hdisj: _:= by exact F.Paths_disjoint
unfold paths_disjoint at hdisj

have hdisj2: Disjoint {v | v ∈ (F.P.get! i).Pa.Wa.support} {v | v ∈ (F.P.get! j).Pa.Wa.support}:= by
  by_cases case: i<j
  apply hdisj
  exact case
  exact hj

  rw[disjoint_comm]
  apply hdisj
  simp at case
  exact Nat.lt_of_le_of_ne case (id (Ne.symm hij))
  exact hi

--have hdisj2: _:= by exact hdisj i j hij hj
have neg: ¬ (Disjoint {v | v ∈ (F.P.get! i).Pa.Wa.support} {v | v ∈ (F.P.get! j).Pa.Wa.support})
:= by
  refine Set.not_disjoint_iff.mpr ?_
  use F.E.get! j
  constructor
  simp only [Set.mem_setOf_eq]
  exact cont

  simp only [Set.mem_setOf_eq]
  exact hhi
exact neg hdisj2


lemma Path_forest_ends_aux_get
(F: PathForest iV iSP H)
(i: ℕ )
(hi: i< F.k)
(v: V)
(hv: v ∈ (F.P.get! i).Pa.Wa.support)
(hv2: v≠ (F.P.get! i).e)
(hk: F.k=F.E.length)
:
v∉ F.E
:= by

by_contra cont
have hex: ∃ (j: Fin (F.E.length)), F.E.get j=v:= by
  exact List.mem_iff_get.mp cont
rcases hex with ⟨j, hj⟩
have hj': F.E.get! j=v:= by
  have h1: F.E.get! j.1=F.E.get ⟨ j.1,j.2⟩ := by
    simp only [List.get!_eq_getD]
    exact List.getD_eq_get F.E default j.isLt
  rw[h1]
  simp
  exact hj

rw[hj'.symm] at hv
have ne: (j:ℕ )≠ i:= by
  by_contra cont2
  have h3: F.E.get! ↑j=(F.P.get! j).e:= by
    apply F.Ends_equal
    exact lt_of_eq_of_lt cont2 hi
  rw[h3] at hj'
  rw[cont2] at hj'
  rw[hj'] at hv2
  exact hv2 rfl

have hhh: F.E.get! j∉  (F.P.get! i).Pa.Wa.support
:= by
  apply Path_forest_ends_inter3
  repeat assumption
  rw[hk]
  exact j.isLt
  exact ne.symm
exact hhh hv


lemma Path_forest_get_end
(F: PathForest iV iSP H)
(i: ℕ )
(hi: i< F.k)
(v: V)
(hv: v ∈ (F.P.get! i).Pa.Wa.support)
(inStarts: v∈  F.E)--.droplast
--(hv2: v≠ (F.P.get! i).s)
(hk: F.k=F.E.length)
:
v= (F.P.get! i).e
:= by
by_contra cont
have hc: v∉  F.E:= by
  exact Path_forest_ends_aux_get iV iSP F i hi v hv cont hk
exact hc inStarts

--used
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
rw[F.Ends_equal i hi]
exact Path_forest_get_end iV iSP F i hi v hv inStarts hk





lemma path_support_eq
(H: Subgraph G)
(x y: V)
(P:SubgraphPath H x y)
:
{v:V|v∈ P.Wa.support}.toFinset.card=P.Wa.length+1
:=by

have h1: P.Wa.support.length=P.Wa.length+1:= by
  --simp only [Walk.length_support]
  simp

have h2: P.Wa.support.toFinset.card={v:V|v∈ P.Wa.support}.toFinset.card:= by
  congr
  ext v
  simp

have h3: P.Wa.support.toFinset.card=P.Wa.support.length:= by
  rw[ List.toFinset_card_of_nodup]
  apply Walk.IsPath.support_nodup
  exact P.Wa_Is_Path
rw[h1.symm, h3.symm, h2]

lemma path_support_eq2
(H: Subgraph G)
(x y: V)
(P:SubgraphPath H x y)
:
P.Wa.support.toFinset.card=P.Wa.length+1
:=by
have h3: P.Wa.support.toFinset.card=P.Wa.support.length:= by
  rw[ List.toFinset_card_of_nodup]
  apply Walk.IsPath.support_nodup
  exact P.Wa_Is_Path
have h1: P.Wa.support.length=P.Wa.length+1:= by
  --simp only [Walk.length_support]
  simp
rw[h1.symm, h3.symm]


lemma long_path_forest_card
(t k: ℕ)
(Fo: PathForest iV iSP H)
(long: Path_forest_long! iV iSP Fo l k)
(hk: k≤ Fo.k)

(ht': t≤  k)
:
((Path_forest_support_until_t iV iSP Fo (t)).toFinset.card)≥ t*l
:= by
have ht: t≤  Fo.k:= by
  exact Nat.le_trans ht' hk
unfold Path_forest_support_until_t
--simp only [Set.mem_setOf_eq]
have supeq: {v :V| ∃ (i:ℕ ), i < t∧  v ∈ (Fo.P.get! i).Pa.Wa.support}.toFinset = (Finset.range t).biUnion  fun x ↦ ((Fo.P.get! x).Pa.Wa.support.toFinset):= by
  ext x
  simp
calc
  _={v :V| ∃ (i:ℕ ), i < t∧  v ∈ (Fo.P.get! i).Pa.Wa.support}.toFinset.card
    := by simp
  _= ((Finset.range t).biUnion  fun x ↦ ((Fo.P.get! x).Pa.Wa.support.toFinset)).card:= by
    congr
  _=∑ (i∈ Finset.range t), ((Fo.P.get! i).Pa.Wa.support.toFinset).card:= by
    refine card_biUnion ?h
    intro i hi j hj hij
    rw [@List.disjoint_toFinset_iff_disjoint]
    have hdis:_:=by exact Fo.Paths_disjoint
    unfold paths_disjoint at hdis
    by_cases case: i<j
    have h1: Disjoint {v | v ∈ (Fo.P.get! i).Pa.Wa.support} {v | v ∈ (Fo.P.get! j).Pa.Wa.support}:= by
      apply hdis
      exact case
      calc
        j<t:= by exact List.mem_range.mp hj
        _≤ Fo.k:= by exact ht
    simp at h1
    apply List.disjoint_left.mpr
    intro a ha
    have ain:a∈ {v | v ∈ (Fo.P.get! i).Pa.Wa.support}:= by
      simp
      exact ha
    have anin: a∉ {v | v ∈ (Fo.P.get! j).Pa.Wa.support}:= by
      by_contra cont
      have neg: ¬ (Disjoint {v | v ∈ (Fo.P.get! i).Pa.Wa.support} {v | v ∈ (Fo.P.get! j).Pa.Wa.support}):= by
        rw [@Set.not_disjoint_iff]
        use a
      exact neg h1
    simp at anin
    exact anin
    --
    simp at case
    have case: j<i:= by
      exact Nat.lt_of_le_of_ne case (id (Ne.symm hij))
    rw[List.disjoint_comm]
    have h1: Disjoint  {v | v ∈ (Fo.P.get! j).Pa.Wa.support} {v | v ∈ (Fo.P.get! i).Pa.Wa.support}:= by
      apply hdis
      exact case
      calc
        i<t:= by exact List.mem_range.mp hi
        _≤ Fo.k:= by exact ht
    simp at h1
    apply List.disjoint_left.mpr
    intro a ha
    have ain:a∈ {v | v ∈ (Fo.P.get! j).Pa.Wa.support}:= by
      simp
      exact ha
    have anin: a∉ {v | v ∈ (Fo.P.get! i).Pa.Wa.support}:= by
      by_contra cont
      have neg: ¬ (Disjoint {v | v ∈ (Fo.P.get! j).Pa.Wa.support} {v | v ∈ (Fo.P.get! i).Pa.Wa.support}):= by
        rw [@Set.not_disjoint_iff]
        use a
      exact neg h1
    simp at anin
    exact anin





  _≥ ∑ (i∈ Finset.range t), l:=by
    gcongr  with i hi
    unfold Path_forest_long! at long
    rw[path_support_eq2]
    calc
      (Fo.P.get! i).Pa.Wa.length + 1
      ≥ (Fo.P.get! i).Pa.Wa.length := by
        simp
      _≥ l:= by
        apply long
        calc
          i<t:= by exact List.mem_range.mp hi
          _≤ k:= by exact ht'



    --





  _= _:= by
    rw [@sum_const]
    simp


---used
lemma single_path_forest_tail_disjoint
(F1 : PathForest iV iSP H)
(k: ℕ )
(F1k: F1.k≥ k)
:
( ∀(i j: ℕ ), (i< j)→ (j<k)→ (tail_disjoint_imp (F1.P.get! i) (F1.P.get! j)))
:= by
intro i j hi hj
have hpathsdisjoint:_:=by exact F1.Paths_disjoint
unfold paths_disjoint at hpathsdisjoint
unfold tail_disjoint_imp
have hj': j<F1.k:= by
  exact Nat.lt_of_lt_of_le hj F1k
have h2:_:= by exact hpathsdisjoint i j hi hj'
simp at h2
intro x hx hx2
have hh2: x∈ {v | v ∈ (F1.P.get! j).Pa.Wa.support}:= by
  simp
  exact List.mem_of_mem_tail hx2
have hh3: x∈ {v | v ∈ (F1.P.get! i).Pa.Wa.support}:= by
  simp
  exact hx
have neg: ¬ (Disjoint {v | v ∈ (F1.P.get! i).Pa.Wa.support} {v | v ∈ (F1.P.get! j).Pa.Wa.support}):= by
  refine Set.Nonempty.not_disjoint ?_
  refine Set.inter_nonempty.mpr ?_
  use x
exact neg (hpathsdisjoint i j hi hj')









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

--used
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
--(hk: F.k=F.S.length)
:
F.S.get! i∈ (F.P.get! i).Pa.Wa.support
:= by
have h1:  (F.P.get! i).s=F.S.get! i:= by
  symm
  exact F.Starts_equal i hi
rw[h1.symm]
exact Walk.start_mem_support (F.P.get! i).Pa.Wa

--not used?
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
  --exact hk

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
--(hk: F.k=F.S.length)
:
F.S.get! j∉  (F.P.get! i).Pa.Wa.support
:= by
by_contra cont
have hhi:  F.S.get! j∈  (F.P.get! j).Pa.Wa.support:= by
  apply Path_forest_starts_inter
  exact hj
  --exact hk

have hdisj: _:= by exact F.Paths_disjoint
unfold paths_disjoint at hdisj

have hdisj2: Disjoint {v | v ∈ (F.P.get! i).Pa.Wa.support} {v | v ∈ (F.P.get! j).Pa.Wa.support}:= by
  by_cases case: i<j
  apply hdisj
  exact case
  exact hj

  rw[disjoint_comm]
  apply hdisj
  simp at case
  exact Nat.lt_of_le_of_ne case (id (Ne.symm hij))
  exact hi

--have hdisj2: _:= by exact hdisj i j hij hj
have neg: ¬ (Disjoint {v | v ∈ (F.P.get! i).Pa.Wa.support} {v | v ∈ (F.P.get! j).Pa.Wa.support})
:= by
  refine Set.not_disjoint_iff.mpr ?_
  use F.S.get! j
  constructor
  simp only [Set.mem_setOf_eq]
  exact cont

  simp only [Set.mem_setOf_eq]
  exact hhi
exact neg hdisj2


---used
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
  have h1: F.S.get! j.1=F.S.get ⟨ j.1,j.2⟩ := by
    simp only [List.get!_eq_getD]
    exact List.getD_eq_get F.S default j.isLt
  rw[h1]
  simp
  exact hj

rw[hj'.symm] at hv
have ne: (j:ℕ )≠ i:= by
  by_contra cont2
  have h3: F.S.get! ↑j=(F.P.get! j).s:= by
    apply F.Starts_equal
    exact lt_of_eq_of_lt cont2 hi
  rw[h3] at hj'
  rw[cont2] at hj'
  rw[hj'] at hv2
  exact hv2 rfl

have hhh: F.S.get! j∉  (F.P.get! i).Pa.Wa.support
:= by
  apply Path_forest_starts_inter3
  repeat assumption
  rw[hk]
  exact j.isLt
  exact ne.symm
exact hhh hv


--used
lemma Path_forest_get_start
(F: PathForest iV iSP H)
(i: ℕ )
(hi: i< F.k)
(v: V)
(hv: v ∈ (F.P.get! i).Pa.Wa.support)
(inStarts: v∈  F.S)--.droplast
--(hv2: v≠ (F.P.get! i).s)
(hk: F.k=F.S.length)
:
v= (F.P.get! i).s
:= by
by_contra cont
have hc: v∉  F.S:= by
  exact Path_forest_starts_aux_get iV iSP F i hi v hv cont hk
exact hc inStarts

--used
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





--used
lemma set_disjoint_to_tail_disjoint_forward
(F1  F2: PathForest iV iSP H)
(Fb': Set V)
(k: ℕ )
(F1k: F1.k≥ k)
(F2k: F2.k≥ k)
(F2k2: F2.k = F2.S.length)
(F2_avoids_Fb: Path_forest_avoids! iV iSP F2 Fb' k)
(F1_in_Fb: {v:V| v∈ Path_forest_support iV iSP F1∧ v∉ F2.S}= Fb')
(hk: F1.k=F1.S.length)
:
∀(i j: ℕ ), (i< k)→ (j<k)→ (tail_disjoint_imp (F1.P.get! i) (F2.P.get! j))
:= by
/-let Fb: Set V:={v:V| v∈ Path_forest_support' iV iSP F1∧ v∉ F2.S.dropLast}
have F2_avoids_Fb: Path_forest_avoids! iV iSP F2 Fb k:= by
  apply path_forest_avoids_monotone!
  exact F2_avoids_Fb
  dsimp [Fb]
  rw[F1_in_Fb.symm]
  simp
  intro a ha1 ha2

have F1_in_Fb:{v:V| v∈ Path_forest_support' iV iSP F1∧ v∉ F2.S.dropLast}= Fb:=by
  dsimp[Fb]-/
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
    _≤ F1.k:= by simp
    _=  F1.P.length:= by exact F1.P_length.symm
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
  apply List.get_mem F1.P i
  exact ha
have inS: a ∈ F2.S:= by
  exact hF1 InSup

have ninS: a ∉ F2.S:=by
  apply Path_forest_starts_aux_get
  have hjl: j<F2.k:= by
    calc
      j<k:= by exact hj
      _≤ F2.k:=by exact F2k
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



--used
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




--used
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










--used
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



--used
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

--used
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



--used
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



--used
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



--used
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


















--used (delete from other file)
lemma set_disjoint_to_internal_disjoint_reverse_taildisj_symm2_tailaligned2
(F1  F2: PathForest iV iSP H)
(Fb: Set V)
(k: ℕ )
(F1k': F1.k> k)
(F2k: F2.k≥ k)
(F2k2: F2.k = F2.S.length)
(F1k2: F1.k = F1.E.length)
(Ends_eq:F1.E=F2.S.rotate 1)
(F2SNodup: F2.E.Nodup)
(F2_avoids_Fb: Path_forest_avoids! iV iSP F2 Fb k)
(F1_in_Fb: {v:V| v∈ Path_forest_support iV iSP F1∧ v∉ F2.S}= Fb)
(hk: F1.k=F1.S.length)
:
∀(j i: ℕ ), (j< k)→ (i<k)→ j≠ i+1→  (tail_disjoint_imp  (F2.P.get! j) (F1.P.get! i))
:= by
have F1k: F1.k≥  k:=by exact Nat.le_of_succ_le F1k'
intro j i hj hi hneq
unfold tail_disjoint_imp
apply List.disjoint_left.mpr
intro a ha
unfold Path_forest_avoids! at F2_avoids_Fb
have h1: Disjoint {v:V|v∈ (F2.P.get! j).Pa.Wa.support} Fb:=by
  apply F2_avoids_Fb
  exact hj
have anin: a∉ Fb:= by
  have ain: a∈ {v:V| v∈ (F2.P.get! j).Pa.Wa.support}:= by
    simp
    exact ha
  by_contra cont
  have neg: ¬(Disjoint {v:V|v∈ (F2.P.get! j).Pa.Wa.support} Fb):=by
    rw [@Set.not_disjoint_iff]
    use a
  exact neg h1
rw [F1_in_Fb.symm] at anin
simp at anin
by_contra cont1
have in2:  a ∈ (F1.P.get! i).Pa.Wa.support:=by
    exact List.mem_of_mem_tail cont1
have ainS: a ∈ F2.S:= by

  have in3: a ∈ Path_forest_support iV iSP F1:= by
      unfold Path_forest_support
      simp
      use (F1.P.get! i)
      constructor
      have h3: F1.P.get! i=F1.P.get ⟨ i, _⟩:= by
        refine (get_eq_get2! iSP F1.P i ?_).symm
        calc
          i<k:= by exact hi
          _≤  F1.k:= by exact F1k
          _=F1.P.length:= by exact F1.P_length.symm
      rw[h3]
      apply List.get_mem F1.P i
      exact in2


  apply anin in3

have aeq: a=(F2.P.get! j).s:= by
  apply Path_forest_get_start
  calc
    j<k:= by exact hj
    _≤ F2.k:= by exact F2k
  exact ha
  exact ainS
  exact F2k2

have aeq2: a=(F2.S.get! j):= by
  apply Path_forest_get_start2
  calc
    j<k:= by exact hj
    _≤ F2.k:= by exact F2k
  exact ha
  exact ainS
  exact F2k2

by_cases jzer: j≠ 0
have aeq3: ((F2.S.rotate 1).get! (j-1))=(F2.S.get! (j)):= by
  let jm:= j-1
  have h1: j=jm+1:= by
    dsimp[jm]
    refine (Nat.sub_eq_iff_eq_add ?h).mp rfl
    exact Nat.one_le_iff_ne_zero.mpr jzer
  rw[h1]
  simp only [add_tsub_cancel_right]
  apply list_rotate_get_V
  dsimp[jm]
  rw [← h1]
  rw[F2k2.symm]
  exact Nat.lt_of_lt_of_le hj F2k

rw[aeq3.symm] at aeq2
rw[Ends_eq.symm] at aeq2
have in4:  a ∈ (F1.P.get! (j-1)).Pa.Wa.support:=by
    rw[aeq2]
    rw[F1.Ends_equal]
    exact Walk.end_mem_support (F1.P.get! (j - 1)).Pa.Wa
    calc
      j-1≤ j:= by simp
      _< k:= by exact hj
      _≤ F1.k:= by exact F1k




have h1:  Disjoint {v:V|v∈ (F1.P.get! (j - 1)).Pa.Wa.support} {v:V|v∈ (F1.P.get! (i)).Pa.Wa.support}:= by
  have h2:_:=by exact  F1.Paths_disjoint
  unfold paths_disjoint at h2
  by_cases case:  j - 1< i
  apply h2 (j-1) i
  exact case
  calc
    i<k:= by exact hi
    _≤ F1.k:= by exact F1k
  simp only [not_lt] at case
  have inew: i<j-1:= by
    rw [@Nat.lt_sub_iff_add_lt']
    rw[add_comm]
    refine Nat.lt_of_le_of_ne ?h₁ (id (Ne.symm hneq))
    refine Nat.add_le_of_le_sub ?h₁.hle case
    exact Nat.one_le_iff_ne_zero.mpr jzer

  rw[disjoint_comm]
  apply h2  i (j-1)
  exact inew
  calc
    j-1≤ j:= by simp
    _< k:= by exact hj
    _≤ F1.k:= by exact F1k

have h1neg: ¬  (Disjoint {v | v ∈ (F1.P.get! (j - 1)).Pa.Wa.support} {v | v ∈ (F1.P.get! i).Pa.Wa.support}):=by
  refine Set.not_disjoint_iff.mpr ?_
  use a
  constructor
  exact in4
  exact in2

exact h1neg h1

simp at jzer
rw[ jzer] at aeq
have aeq4: a=(F1.E.get! (F1.k-1)):= by
  rw[jzer] at aeq2
  rw[Ends_eq]
  rw[aeq2]
  have F1keq: F1.k=F2.k:= by
    rw[F1k2, F2k2, Ends_eq]
    simp
  rw[F1keq, F2k2]
  symm
  apply list_rotate_get_V_last
  exact List.length_pos_of_mem ainS


have h1:  Disjoint {v:V|v∈ (F1.P.get! (i)).Pa.Wa.support} {v:V|v∈ (F1.P.get! (F1.k-1)).Pa.Wa.support}:= by
  have h2:_:=by exact  F1.Paths_disjoint
  unfold paths_disjoint at h2
  by_cases case:  i< F1.k-1
  apply h2 i (F1.k-1)
  exact case
  refine Nat.sub_one_lt_of_le ?_ ?_
  calc
    F1.k≥ k:= by exact F1k
    _> i:= by exact hi
    _≥ 0:= by simp
  simp

  exfalso
  simp at case
  have iieq : i+1< F1.k:=by
    calc
      i+1≤ k:= by exact hi
      _< F1.k:= by exact F1k'
  have neg:¬ ( i + 1 < F1.k):=by
    simp
    exact case
  exact neg  iieq




have in4:  a ∈ (F1.P.get! (F1.k-1)).Pa.Wa.support:=by
    rw[aeq4]
    rw[F1.Ends_equal]
    exact Walk.end_mem_support (F1.P.get! (F1.k - 1)).Pa.Wa
    refine Nat.sub_lt ?_ ?_
    exact Nat.zero_lt_of_lt F1k'
    simp


have h1neg: ¬  (Disjoint {v | v ∈ (F1.P.get! (i)).Pa.Wa.support} {v | v ∈ (F1.P.get! (F1.k-1)).Pa.Wa.support}):=by
  refine Set.not_disjoint_iff.mpr ?_
  use a
  constructor
  exact in2
  exact in4

exact h1neg h1
