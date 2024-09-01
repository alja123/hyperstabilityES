import MyProject.J_bound
open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 200000

universe u
variable {V : Type u} {G : SimpleGraph V}
variable   [Fintype V]--[FinV: Fintype V]
variable  [DecidableRel G.Adj] --[DecG: DecidableRel G.Adj]
variable [Fintype (Sym2 V)]-- [FinV2: Fintype (Sym2 V)]
variable {p m κ pr h α : ℕ}
variable {κPositive: κ >0}
variable {pPositive: p >0}
variable {mPositive: m >0}
variable {hPositive: h >0}
variable {prPositive: pr >0}
--variable {γPositive: γ >0}
variable (iI:Inhabited (Clump G p m κ pr h))
variable (iV:Inhabited V)
variable (iSub:Inhabited (Subgraph G))






variable (pLarge: p≥ 20)
variable (prggp: pr ≥ gg2 p)
variable (hggp: h ≥ gg1 pr)
variable (κggh: κ ≥ gg1 h)
variable (mggκ :m≥ gg2 κ )
variable (κggα: κ ≥ gg1 α )
variable (αggh: α ≥ h)

lemma Jset_disjoint
--(L: Locally_Dense G p m h)
(Ord: List (Clump G p m κ pr h))
--(Decomp: Clump_Decomposition L (Ord.toFinset))
:
∀ (i j: ℕ),
i<j→j<Ord.length→
(Disjoint (JClump p m κ pr h iI i Ord).verts (JClump p m κ pr h iI j Ord).verts)
:= by
intro i j hi hj
unfold JClump
have h1: (CovM p m κ pr h (Ord.get! j)).verts ⊆  list_union p m κ pr h (List.drop (i + 1) Ord):= by
  unfold CovM
  unfold list_union
  unfold list_BSet
  intro v hv
  simp
  simp at hv
  rcases hv with case|case
  use (Ord.getD j default)
  constructor
  have ap: Ord=Ord.take (i+1) ++ Ord.drop (i+1):= by
    simp
  nth_rewrite 1 [ap]
  rw[List.getD_append_right]
  simp
  have hmin: min (i + 1) Ord.length=i+1:= by
    simp
    calc
      i+1≤ j:= by
        exact hi
      _≤  Ord.length:= by exact Nat.le_of_succ_le hj
  rw[hmin]
  have hlelen: j - (i + 1)<(List.drop (i + 1) Ord).length:= by
    simp
    exact (Nat.sub_lt_sub_iff_right hi).mpr hj
  have hget: (List.drop (i + 1) Ord).getD (j - (i + 1)) default=(List.drop (i + 1) Ord).get ⟨ (j - (i + 1)), hlelen ⟩:= by
    exact List.getD_eq_get (List.drop (i + 1) Ord) default hlelen
  rw[hget]
  exact List.get_mem (List.drop (i + 1) Ord) (j - (i + 1)) hlelen

  simp
  left
  exact hi
  exact case

  have case: v∈ BSetPlusM (Ord.getD j default):= by
    unfold BSetPlusM
    simp
    right
    exact case

  use (Ord.getD j default)
  constructor
  have ap: Ord=Ord.take (i+1) ++ Ord.drop (i+1):= by
    simp
  nth_rewrite 1 [ap]
  rw[List.getD_append_right]
  simp
  have hmin: min (i + 1) Ord.length=i+1:= by
    simp
    calc
      i+1≤ j:= by
        exact hi
      _≤  Ord.length:= by exact Nat.le_of_succ_le hj
  rw[hmin]
  have hlelen: j - (i + 1)<(List.drop (i + 1) Ord).length:= by
    simp
    exact (Nat.sub_lt_sub_iff_right hi).mpr hj
  have hget: (List.drop (i + 1) Ord).getD (j - (i + 1)) default=(List.drop (i + 1) Ord).get ⟨ (j - (i + 1)), hlelen ⟩:= by
    exact List.getD_eq_get (List.drop (i + 1) Ord) default hlelen
  rw[hget]
  exact List.get_mem (List.drop (i + 1) Ord) (j - (i + 1)) hlelen

  simp
  left
  exact hi
  exact case





apply Set.disjoint_iff_forall_ne.mpr
intro v hv u hu
--simp
simp at hv hu
have hu1: u∈ list_union p m κ pr h (List.drop (i + 1) Ord):= by
  simp at h1
  exact h1 hu.1
have hv1: v ∉ list_union p m κ pr h (List.drop (i + 1) Ord):= by
  apply hv.2
  have hv2: v ∈ (CovM p m κ pr h (Ord.getD i default)).verts:= by
    exact hv.1
  unfold CovM at hv2
  simp at hv2
  rcases hv2 with case1|case1
  exact case1
  unfold BSetPlusM
  simp
  right
  exact case1
exact Ne.symm (ne_of_mem_of_not_mem hu1 hv1)



lemma Jset_disjoint_ne
--(L: Locally_Dense G p m h)
(Ord: List (Clump G p m κ pr h))
--(Decomp: Clump_Decomposition L (Ord.toFinset))
:
∀ (i j: ℕ),
i<Ord.length→j<Ord.length→i≠ j→
(Disjoint (JClump p m κ pr h iI i Ord).verts (JClump p m κ pr h iI j Ord).verts)
:= by
intro i j hi hj hdif
have h1: i<j∨ j<i:= by
  exact Nat.lt_or_gt_of_ne hdif
rcases h1 with case|case
apply Jset_disjoint
repeat assumption

rw [@disjoint_comm]
apply Jset_disjoint
repeat assumption

lemma Jset_no_edges
--(L: Locally_Dense G p m h)
(Ord: List (Clump G p m κ pr h))
(Sub: Subgraph G)
(hSub: Sub= sSup {Oi: Subgraph G| ∃ (i:ℕ), i <Ord.length∧  Oi=JClump p m κ pr h iI i Ord})
--(Decomp: Clump_Decomposition L (Ord.toFinset))
:
∀ (i j: ℕ), ∀ (u v: V),
i<Ord.length→j<Ord.length→ i≠ j→ u∈ (JClump p m κ pr h iI i Ord).verts→ v∈  (JClump p m κ pr h iI j Ord).verts
→ ¬ (Sub.Adj u v)
:= by
intro i j u v hi hj hdif hu hv
rw[hSub]
simp
intro Kt t ht hKt
by_contra cont
have huin: u∈ (JClump p m κ pr h iI t Ord).verts:= by
  rw[hKt.symm]
  exact Kt.edge_vert cont
have hvin: v∈ (JClump p m κ pr h iI t Ord).verts:= by
  rw[hKt.symm]
  exact Kt.edge_vert (id (Subgraph.adj_symm Kt cont))
have nDisj_it: ¬(Disjoint (JClump p m κ pr h iI t Ord).verts (JClump p m κ pr h iI i Ord).verts):= by
  refine Set.not_disjoint_iff.mpr ?_
  use u
have nDisj_jt: ¬(Disjoint (JClump p m κ pr h iI t Ord).verts (JClump p m κ pr h iI j Ord).verts):= by
  refine Set.not_disjoint_iff.mpr ?_
  use v



have ti: t=i:= by
    by_contra cont
    simp at cont
    have dis:Disjoint (JClump p m κ pr h iI t Ord).verts (JClump p m κ pr h iI i Ord).verts:= by
      apply Jset_disjoint_ne
      repeat assumption
    exact nDisj_it dis

have tj: t=j:= by
    by_contra cont
    simp at cont
    have dis:Disjoint (JClump p m κ pr h iI t Ord).verts (JClump p m κ pr h iI j Ord).verts:= by
      apply Jset_disjoint_ne
      repeat assumption
    exact nDisj_jt dis

rw[ti] at tj
exact hdif tj


def JCover (i: ℕ ) (Ord: List (Clump G p m κ pr h)): Set V:=
((sSup (Ord.get! i).M: Subgraph G).verts)



lemma JSet_covered_by_M
(Ord: List (Clump G p m κ pr h))
(Sub: Subgraph G)
(hSub: Sub= sSup {Oi: Subgraph G| ∃ (i:ℕ), i <Ord.length∧  Oi=JClump p m κ pr h iI i Ord})
:
∀ (i: ℕ),∀ (u v:V),
i<Ord.length→
(u∈ (JClump p m κ pr h iI i Ord).verts)
→(v∈ (JClump p m κ pr h iI i Ord).verts)
→(Sub.Adj u v)
→ (u∈ JCover iI  i Ord)∨(v∈ JCover iI i Ord)
:= by
intro i u v hi hu hv hedge
rw[hSub] at hedge
simp at hedge
rcases hedge with ⟨ Kt, tex, hadj⟩
rcases tex with ⟨t, ht1, ht2 ⟩

have huin: u∈ (JClump p m κ pr h iI t Ord).verts:= by
  rw[ht2.symm]
  exact Kt.edge_vert hadj
have hvin: v∈ (JClump p m κ pr h iI t Ord).verts:= by
  rw[ht2.symm]
  exact Kt.edge_vert (id (Subgraph.adj_symm Kt hadj))
have nDisj_it: ¬(Disjoint (JClump p m κ pr h iI t Ord).verts (JClump p m κ pr h iI i Ord).verts):= by
  refine Set.not_disjoint_iff.mpr ?_
  use u

have ti: t=i:= by
    by_contra cont
    simp at cont
    have dis:Disjoint (JClump p m κ pr h iI t Ord).verts (JClump p m κ pr h iI i Ord).verts:= by
      apply Jset_disjoint_ne
      repeat assumption
    exact nDisj_it dis
rw[ht2, ti] at hadj
unfold JClump at hadj
unfold CovM at hadj
simp at hadj
unfold JCover
simp
aesop
/-theorem version1
(L: Locally_Dense G p m h)
(LNonempty: L.H.Nonempty )
(no_paths: ¬ Has_length_d_path (L.Gr) (h*m))
:
∃ (Ord: List (Clump G p m κ pr h)),
Clump_Decomposition L (Ord.toFinset)
∧
(∀ (i: ℕ ),
i≤ Ord.length→
p*(JClump p m κ pr h iI i Ord).edgeSet.toFinset.card
-/





lemma JCover_bound
(Ord: List (Clump G p m κ pr h))
(narrow: Clump_family_narrow  (Ord.toFinset))
:
∀ (i: ℕ),
i<Ord.length→
(JCover iI  i Ord).toFinset.card≤ κ *m
:= by
intro i hi
unfold JCover
unfold Clump_family_narrow at narrow

have hineq: κ ≥ h * 4 ^ (pr * pr * h):= by
  have hin2: h*h*h≥ (pr * pr * h):= by
    gcongr
    apply gg1_ge
    repeat assumption
    apply gg1_ge
    repeat assumption

  calc
      κ ≥ h*4^(h*h*h):= by
        apply gg1_5
        repeat assumption
      _≥ h* 4^(pr*pr*h):= by
        gcongr h*?_
        gcongr
        simp

        /-apply gg1_ge
        repeat assumption
        apply gg1_ge
        repeat assumption-/
--simp
calc
  _=
  (sSup (Ord.get! i).M: Subgraph G).verts.toFinset.card:= by
    simp --
  _≤ (Ord.get! i).C.verts.toFinset.card:= by
    gcongr
    simp
    exact fun i_1 i_2 ↦ M_verts_contained_in_C_verts_set i_2
  _≤ m*h* 4^((Ord.get! i).k):= by
    exact (Ord.get! i).C_Order
  _≤m*h* 4^(pr*pr*h):= by
    gcongr
    simp
    apply narrow
    simp
    have hin: Ord.getD i default = Ord.get ⟨ i, hi⟩:= by
      exact List.getD_eq_get Ord default hi
    rw[hin]
    exact List.get_mem Ord i hi
    --

  _=h* 4^(pr*pr*h)*m:= by ring_nf
  _≤ κ *m:= by
    gcongr

    --ring_nf

    /-calc
      κ ≥ h*4^(h*h*h):= by
        sorry
        --apply gg1_5
        --repeat assumption
      _≥ h* 4^(pr*pr*h):= by
        sorry
        /-gcongr
        apply gg1_ge
        repeat assumption
        apply gg1_ge
        repeat assumption-/-/




lemma sum_Jsets
(Ord: List (Clump G p m κ pr h))
(n:ℕ )
(hn:n≤ Ord.length)
:
(sSup {Oi: Subgraph G| ∃ (i:ℕ), i <n∧  Oi=JClump p m κ pr h iI i Ord}).edgeSet.toFinset.card
=∑ i∈  (Finset.range n), (JClump p m κ pr h iI i Ord).edgeSet.toFinset.card
:=by
induction' n with n IH
simp
--have hSum:
--  ∑ i ∈  (Finset.range (n+1) ), (JClump p m κ pr h iI (i) Ord).edgeSet.toFinset.card
--  =∑ i ∈  (Finset.range n), (JClump p m κ pr h iI (i) Ord).edgeSet.toFinset.card
--  + (JClump p m κ pr h iI (i) Ord).edgeSet.toFinset.card:=by

by_cases case0: n=0
rw[case0]
simp


have hSum:
  ∑ i ∈  (Finset.range (n+1) ), (JClump p m κ pr h iI (i) Ord).edgeSet.toFinset.card
  =∑ i ∈  (Finset.range n), (JClump p m κ pr h iI (i) Ord).edgeSet.toFinset.card
  +∑ i ∈  ({n}: Finset ℕ ), (JClump p m κ pr h iI (i) Ord).edgeSet.toFinset.card:=by
    exact sum_range_succ (fun x ↦ (JClump p m κ pr h iI x Ord).edgeSet.toFinset.card) n
simp only [  sum_singleton] at hSum

/-
have hSum:
  ∑ i ∈  (Finset.range ((n-1)+1) ), (JClump p m κ pr h iI (i) Ord).edgeSet.toFinset.card
  =∑ i ∈  (Finset.range (n-1)), (JClump p m κ pr h iI (i) Ord).edgeSet.toFinset.card
  +∑ i ∈  ({n-1}: Finset ℕ ), (JClump p m κ pr h iI (i) Ord).edgeSet.toFinset.card:=by
    exact sum_range_succ (fun x ↦ (JClump p m κ pr h iI x Ord).edgeSet.toFinset.card) (n - 1)
simp only [  sum_singleton] at hSum
have hnm1: n-1+1=n:= by
  exact Nat.succ_pred_eq_of_ne_zero case0
rw[hnm1] at hSum-/
have hSup:
  ( {Oi: Subgraph G| ∃ (i:ℕ), i <n+1∧  Oi=JClump p m κ pr h iI i Ord})
  =( {Oi: Subgraph G| ∃ (i:ℕ), i <(n)∧  Oi=JClump p m κ pr h iI i Ord})
  ∪   {(JClump p m κ pr h iI (n) Ord)} := by
    /-by_cases case2: n=1
    rw[case2]
    simp
    exact Set.singleton_def (JClump p m κ pr h iI 0 Ord)

    simp at case2-/



    ext oi
    simp
    constructor
    intro hh
    rcases hh with ⟨i, hi ⟩
    by_cases case: i<n
    right
    use i
    constructor
    exact case
    exact hi.2

    have h2: i<n+1:= by exact hi.1
    simp at case
    have h3: i=n:=by
      exact Nat.eq_of_le_of_lt_succ case h2
    left
    rw [h3.symm]
    exact hi.2

    intro hh
    rcases hh with case1|case1
    use n
    constructor
    simp

    exact case1

    rcases case1 with ⟨i, hi ⟩
    use i
    constructor
    calc
      i<n:=by exact hi.1
      _≤ n+1:=by simp
    exact hi.2


have hunion:
  (sSup {Oi: Subgraph G| ∃ (i:ℕ), i <n+1∧  Oi=JClump p m κ pr h iI i Ord}).edgeSet.toFinset
  =(sSup {Oi: Subgraph G| ∃ (i:ℕ), i <(n)∧  Oi=JClump p m κ pr h iI i Ord}).edgeSet.toFinset
  ∪ ((JClump p m κ pr h iI (n) Ord).edgeSet.toFinset):= by
    rw[hSup]
    simp
    ext e
    simp
    exact Or.comm

have disj: Disjoint (sSup {Oi: Subgraph G| ∃ (i:ℕ), i <(n)∧  Oi=JClump p m κ pr h iI i Ord}).edgeSet.toFinset ((JClump p m κ pr h iI (n) Ord).edgeSet.toFinset):= by
  simp
  intro i hi
  refine Set.disjoint_iff_forall_ne.mpr ?_
  intro a ha b hb
  have hxyex: ∃ (a1 a2:V), a=s(a1,a2):= by
    exact Sym2_to_tuple a
  have hbxyex: ∃ (b1 b2:V), b=s(b1,b2):= by
    exact Sym2_to_tuple b
  rcases hxyex with ⟨a1, a2, ha1a1 ⟩
  rcases hbxyex with ⟨b1, b2, hb1b1 ⟩
  rw[ha1a1] at ha
  have ha1in: a1∈ (JClump p m κ pr h iI i Ord).verts:=by
    exact (JClump p m κ pr h iI i Ord).edge_vert ha

  have disj: Disjoint (JClump p m κ pr h iI i Ord).verts (JClump p m κ pr h iI n Ord).verts:= by
    apply Jset_disjoint
    exact hi
    exact hn
  have anin: a1∉ (JClump p m κ pr h iI n Ord).verts:= by
    by_contra cont
    have neg: ¬(Disjoint (JClump p m κ pr h iI i Ord).verts (JClump p m κ pr h iI n Ord).verts):= by
      refine Set.not_disjoint_iff.mpr ?_
      use a1
    exact neg disj
      --
  rw[hb1b1] at hb
  have hb1in: b1∈ (JClump p m κ pr h iI n Ord).verts:=by
      exact (JClump p m κ pr h iI n Ord).edge_vert hb--
  have hb2in: b2∈ (JClump p m κ pr h iI n Ord).verts:=by
      exact Subgraph.Adj.snd_mem hb
  have ha1ne:a1≠ b1:= by
    by_contra cont
    rw[cont] at anin
    exact anin hb1in
  have ha2ne:a1≠ b2:= by
    by_contra cont
    rw[cont] at anin
    exact anin hb2in
  rw[hb1b1, ha1a1]
  by_contra cont
  simp at cont
  rcases cont with ⟨ case1, case2⟩ | ⟨ case1, case2⟩
  exact ha1ne case1
  exact ha2ne case1

--rw[hunion]
calc
  _=(sSup {Oi: Subgraph G| ∃ (i:ℕ), i <n+1∧  Oi=JClump p m κ pr h iI i Ord}).edgeSet.toFinset.card:= by
    simp
  _=((sSup {Oi: Subgraph G| ∃ (i:ℕ), i <(n)∧  Oi=JClump p m κ pr h iI i Ord}).edgeSet.toFinset
  ∪ ((JClump p m κ pr h iI (n) Ord).edgeSet.toFinset)).card:= by
    congr;
  _=
  (sSup {Oi | ∃ i < n , Oi = JClump p m κ pr h iI i Ord}).edgeSet.toFinset.card
  +((JClump p m κ pr h iI (n) Ord).edgeSet.toFinset).card:= by
    exact card_disjoint_union disj
  _=∑ i ∈  (Finset.range (n)), (JClump p m κ pr h iI (i) Ord).edgeSet.toFinset.card
  +∑ i ∈  ({n}: Finset ℕ ), (JClump p m κ pr h iI (i) Ord).edgeSet.toFinset.card
    :=by
      simp only [sum_singleton]
      --simp only [Subgraph.edgeSet_sSup, Set.mem_setOf_eq, Set.iUnion_exists, Set.biUnion_and',
        --Set.iUnion_iUnion_eq_left, Set.toFinset_card, Fintype.card_ofFinset, Set.mem_iUnion,
        --exists_prop, sum_singleton, add_left_inj]
      congr
      apply IH
      exact Nat.le_of_succ_le hn

  _=_:= by
    exact hSum.symm





lemma sum_Grs_aux
(L: Locally_Dense G p m h)
--(LNonempty: L.H.Nonempty )
(Ord: List (Clump G p m κ pr h))
(decomp: Clump_Decomposition L (Ord.toFinset))
(n: ℕ )
(hn: n≤ Ord.length)
(nodup: Ord.Nodup)
:
(sSup {Oi: Subgraph G| ∃ (i:ℕ), (i <n)∧  Oi=(Ord.get! i).Gr}).edgeSet.toFinset.card
=∑ i∈  (Finset.range (n)), (Ord.get! i).Gr.edgeSet.toFinset.card
:= by

induction' n with n IH
simp
--have hSum:
--  ∑ i ∈  (Finset.range (n+1) ), (JClump p m κ pr h iI (i) Ord).edgeSet.toFinset.card
--  =∑ i ∈  (Finset.range n), (JClump p m κ pr h iI (i) Ord).edgeSet.toFinset.card
--  + (JClump p m κ pr h iI (i) Ord).edgeSet.toFinset.card:=by

by_cases case0: n=0
rw[case0]
simp


have hSum:
  ∑ i ∈  (Finset.range (n+1) ), ((Ord.get! i).Gr).edgeSet.toFinset.card
  =∑ i ∈  (Finset.range n), ((Ord.get! i).Gr).edgeSet.toFinset.card
  +∑ i ∈  ({n}: Finset ℕ ), ((Ord.get! i).Gr).edgeSet.toFinset.card:=by
    exact sum_range_succ (fun x ↦ ((Ord.get! x).Gr).edgeSet.toFinset.card) n
simp only [  sum_singleton] at hSum

/-
have hSum:
  ∑ i ∈  (Finset.range ((n-1)+1) ), (JClump p m κ pr h iI (i) Ord).edgeSet.toFinset.card
  =∑ i ∈  (Finset.range (n-1)), (JClump p m κ pr h iI (i) Ord).edgeSet.toFinset.card
  +∑ i ∈  ({n-1}: Finset ℕ ), (JClump p m κ pr h iI (i) Ord).edgeSet.toFinset.card:=by
    exact sum_range_succ (fun x ↦ (JClump p m κ pr h iI x Ord).edgeSet.toFinset.card) (n - 1)
simp only [  sum_singleton] at hSum
have hnm1: n-1+1=n:= by
  exact Nat.succ_pred_eq_of_ne_zero case0
rw[hnm1] at hSum-/
have hSup:
  ( {Oi: Subgraph G| ∃ (i:ℕ), i <n+1∧  Oi=(Ord.get! i).Gr})
  =( {Oi: Subgraph G| ∃ (i:ℕ), i <(n)∧  Oi=(Ord.get! i).Gr})
  ∪   {(Ord.get! n).Gr} := by
    /-by_cases case2: n=1
    rw[case2]
    simp
    exact Set.singleton_def (JClump p m κ pr h iI 0 Ord)

    simp at case2-/



    ext oi
    simp
    constructor
    intro hh
    rcases hh with ⟨i, hi ⟩
    by_cases case: i<n
    right
    use i
    constructor
    exact case
    exact hi.2

    have h2: i<n+1:= by exact hi.1
    simp at case
    have h3: i=n:=by
      exact Nat.eq_of_le_of_lt_succ case h2
    left
    rw [h3.symm]
    exact hi.2

    intro hh
    rcases hh with case1|case1
    use n
    constructor
    simp

    exact case1

    rcases case1 with ⟨i, hi ⟩
    use i
    constructor
    calc
      i<n:=by exact hi.1
      _≤ n+1:=by simp
    exact hi.2


have hunion:
  (sSup {Oi: Subgraph G| ∃ (i:ℕ), i <n+1∧  Oi=(Ord.get! i).Gr}).edgeSet.toFinset
  =(sSup {Oi: Subgraph G| ∃ (i:ℕ), i <(n)∧  Oi=(Ord.get! i).Gr}).edgeSet.toFinset
  ∪ ((Ord.get! n).Gr.edgeSet.toFinset):= by
    rw[hSup]
    simp
    ext e
    simp
    exact Or.comm

have disj: Disjoint (sSup {Oi: Subgraph G| ∃ (i:ℕ), i <(n)∧  Oi=(Ord.get! i).Gr}).edgeSet.toFinset ((Ord.get! n).Gr.edgeSet.toFinset):= by
  simp
  have hdi: _:= by exact decomp.1
  unfold Clump_family_edge_disjoint  at hdi
  intro i hi
  have hemp: (Ord.getD i default).Gr.edgeSet∩  (Ord.getD n default).Gr.edgeSet=∅ :=by
    have il: i< Ord.length:= by
      exact Nat.lt_trans hi hn
    have nl: n< Ord.length:= by
      exact hn
    have geti: Ord.getD i default=Ord.get ⟨ i,il⟩:= by
      exact List.getD_eq_get Ord default il
    have getn: Ord.getD n default=Ord.get ⟨ n,nl⟩:= by
      exact List.getD_eq_get Ord default nl

    apply hdi
    rw[geti]
    simp
    exact List.get_mem Ord i il
    rw[getn]
    simp
    exact List.get_mem Ord n nl

    rw[geti, getn]
    by_contra cont
    have neg: ¬ (Ord.Nodup):= by

      apply List.not_nodup_of_get_eq_of_ne Ord
      exact cont
      simp
      exact Nat.ne_of_lt hi

    exact neg nodup



    --

  simp at hemp
  rw [← @Set.disjoint_iff_inter_eq_empty] at hemp
  exact hemp


  /-simp
  intro i hi
  refine Set.disjoint_iff_forall_ne.mpr ?_
  intro a ha b hb
  have hxyex: ∃ (a1 a2:V), a=s(a1,a2):= by
    exact Sym2_to_tuple a
  have hbxyex: ∃ (b1 b2:V), b=s(b1,b2):= by
    exact Sym2_to_tuple b
  rcases hxyex with ⟨a1, a2, ha1a1 ⟩
  rcases hbxyex with ⟨b1, b2, hb1b1 ⟩
  rw[ha1a1] at ha
  have ha1in: a1∈ ((Ord.get! i).Gr).verts:=by
    exact ((Ord.get! i).Gr).edge_vert ha

  have disj: Disjoint ((Ord.get! i).Gr).verts (Ord.get! n).Gr.verts:= by
    sorry
  have anin: a1∉ (JClump p m κ pr h iI n Ord).verts:= by
    by_contra cont
    have neg: ¬(Disjoint ((Ord.get! i).Gr).verts (JClump p m κ pr h iI n Ord).verts):= by
      refine Set.not_disjoint_iff.mpr ?_
      use a1
    exact neg disj
      --
  rw[hb1b1] at hb
  have hb1in: b1∈ (JClump p m κ pr h iI n Ord).verts:=by
      exact (JClump p m κ pr h iI n Ord).edge_vert hb--
  have hb2in: b2∈ (JClump p m κ pr h iI n Ord).verts:=by
      exact Subgraph.Adj.snd_mem hb
  have ha1ne:a1≠ b1:= by
    by_contra cont
    rw[cont] at anin
    exact anin hb1in
  have ha2ne:a1≠ b2:= by
    by_contra cont
    rw[cont] at anin
    exact anin hb2in
  rw[hb1b1, ha1a1]
  by_contra cont
  simp at cont
  rcases cont with ⟨ case1, case2⟩ | ⟨ case1, case2⟩
  exact ha1ne case1
  exact ha2ne case1-/

--rw[hunion]
calc
  _=(sSup {Oi: Subgraph G| ∃ (i:ℕ), i <n+1∧  Oi=(Ord.get! i).Gr}).edgeSet.toFinset.card:= by
    simp
  _=((sSup {Oi: Subgraph G| ∃ (i:ℕ), i <(n)∧  Oi=(Ord.get! i).Gr}).edgeSet.toFinset
  ∪ (((Ord.get! n).Gr).edgeSet.toFinset)).card:= by
    congr;
  _=
  (sSup {Oi | ∃ i < n , Oi = (Ord.get! i).Gr}).edgeSet.toFinset.card
  +((Ord.get! n).Gr.edgeSet.toFinset).card:= by
    exact card_disjoint_union disj
  _=∑ i ∈  (Finset.range (n)), ((Ord.get! i).Gr).edgeSet.toFinset.card
  +∑ i ∈  ({n}: Finset ℕ ), ((Ord.get! i).Gr).edgeSet.toFinset.card
    :=by
      simp only [sum_singleton]
      --simp only [Subgraph.edgeSet_sSup, Set.mem_setOf_eq, Set.iUnion_exists, Set.biUnion_and',
        --Set.iUnion_iUnion_eq_left, Set.toFinset_card, Fintype.card_ofFinset, Set.mem_iUnion,
        --exists_prop, sum_singleton, add_left_inj]
      congr
      apply IH
      exact Nat.le_of_succ_le hn

  _=_:= by
    exact hSum.symm





lemma sum_Grs
(L: Locally_Dense G p m h)
(Ord: List (Clump G p m κ pr h))
(decomp: Clump_Decomposition L (Ord.toFinset))
(nodup: Ord.Nodup)
:
L.Gr.edgeSet.toFinset.card
=∑ i∈  (Finset.range (Ord.length)), (Ord.get! i).Gr.edgeSet.toFinset.card
:= by
unfold Clump_Decomposition at decomp
have ssup: L.Gr.edgeSet=(sSup {Oi: Subgraph G| ∃ (i:ℕ), (i ∈ Finset.range (Ord.length))∧  Oi=(Ord.get! i).Gr}).edgeSet:= by
  rw[L.H_Partition_K.symm]
  simp
  ext e
  simp
  constructor
  intro hh
  unfold L_contained_in_clump_family at decomp
  rcases hh with ⟨ Li, hLi1, hLi2⟩
  have hkex: ∃ Kj ∈ Ord.toFinset, Li ≤ Kj.Gr:= by
    apply decomp.2.2
    exact hLi1
  rcases hkex with ⟨Kj, hKj1, hKj2 ⟩
  have ein: e∈ Kj.Gr.edgeSet:= by
    have h1: Li.edgeSet ⊆ Kj.Gr.edgeSet:=by
      exact subgraph_implies_edgesets_subsets hKj2
    exact h1 hLi2
  simp at hKj1
  have iex: ∃ (i: Fin (Ord.length)), Ord.get i=Kj:= by
    exact List.mem_iff_get.mp hKj1
  rcases iex with ⟨i, hi ⟩
  use i
  constructor
  exact i.isLt
  have gete: (Ord.getD (i.1) default)=Ord.get ⟨ i.1, i.2⟩ :=by
    symm
    exact (List.getD_eq_get Ord default i.isLt).symm
  rw[gete]
  simp
  rw[hi]
  exact ein

  intro hh
  rcases hh with ⟨ i, hi1, hi2⟩
  unfold Clump_family_contained_in_L  at decomp
  have hin: (Ord.getD i default)∈ Ord.toFinset:= by
    simp
    refine List.mem_iff_get.mpr ?_
    use ⟨i, hi1 ⟩
    exact (List.getD_eq_get Ord default hi1).symm
  have hcont: (Ord.getD i default).Gr ≤ L.Gr:= by
    apply decomp.2.1
    exact hin
  have ein: e∈ L.Gr.edgeSet:= by
    have h1: (Ord.getD i default).Gr.edgeSet ≤ L.Gr.edgeSet:= by
      exact Subgraph.edgeSet_mono hcont
    exact h1 hi2
  rw[L.H_Partition_K.symm] at ein
  simp at ein
  exact ein
rw[ssup]


have hrw2: {Oi: Subgraph G| ∃ (i:ℕ), (i ∈ Finset.range (Ord.length))∧  Oi=(Ord.get! i).Gr}
  ={Oi: Subgraph G| ∃ (i:ℕ), (i <Ord.length)∧  Oi=(Ord.get! i).Gr}:= by
    simp
rw[hrw2]
apply sum_Grs_aux
exact decomp
simp
exact nodup



lemma sum_Grs_sub_approx
(L: Locally_Dense G p m h)
(Ord: List (Clump G p m κ pr h))
(decomp: Clump_Decomposition L (Ord.toFinset))
(nodup: Ord.Nodup)
(Sub: Subgraph G)
(hSub: Sub= sSup {Oi: Subgraph G| ∃ (i:ℕ), i <Ord.length∧  Oi=JClump p m κ pr h iI i Ord})
(approx: ∀ (i: ℕ ),
i≤ Ord.length→
p*(JClump p m κ pr h iI i Ord).edgeSet.toFinset.card
+
 ((Ord.get! i)).Gr.edgeSet.toFinset.card
≥
p*(Ord.get! i).Gr.edgeSet.toFinset.card
)
:
(p*Sub.edgeSet.toFinset.card+ L.Gr.edgeSet.toFinset.card≥ p*L.Gr.edgeSet.toFinset.card)
:= by
--rw[hSub]
have jbound:
  (sSup {Oi: Subgraph G| ∃ (i:ℕ), i <(Ord.length)∧  Oi=JClump p m κ pr h iI i Ord}).edgeSet.toFinset.card
  =∑ i∈  (Finset.range (Ord.length)), (JClump p m κ pr h iI i Ord).edgeSet.toFinset.card
  :=by
    apply sum_Jsets
    simp
rw[hSub.symm] at jbound


have lbound:
  L.Gr.edgeSet.toFinset.card
  =∑ i∈  (Finset.range (Ord.length)), (Ord.get! i).Gr.edgeSet.toFinset.card
  :=by
    apply sum_Grs
    exact decomp
    exact nodup
rw[jbound, lbound]
rw [mul_sum]
rw [mul_sum]
rw[Finset.sum_add_distrib.symm]
gcongr with  i hi
apply approx
exact mem_range_le hi

lemma theorem_conversion
(L: Locally_Dense G p m h)
(Ord: List (Clump G p m κ pr h))
(decomp: Clump_Decomposition L (Ord.toFinset))
(approx: ∀ (i: ℕ ),
i≤ Ord.length→
p*(JClump p m κ pr h iI i Ord).edgeSet.toFinset.card
+
 ((Ord.get! i)).Gr.edgeSet.toFinset.card
≥
p*(Ord.get! i).Gr.edgeSet.toFinset.card
)
(narrow: Clump_family_narrow  (Ord.toFinset))
(nodup:Ord.Nodup)
:
∃(Sub: Subgraph G), ∃ (Com Cov: List (Set V)),
(∀ (v: V), v∈ Sub.verts→ ∃ (i: ℕ ), (i< Com.length)∧
v∈ (Com.get! i) )
∧
(∀ (i j: ℕ),i<Com.length→j<Com.length→i≠ j→
(Disjoint (Com.get! i) (Com.get! j)))
∧
(∀ (i j: ℕ), ∀ (u v: V),i<Com.length→j<Com.length→ i≠ j→
u∈ (Com.get! i)→ v∈   (Com.get! j)
→ ¬ (Sub.Adj u v))
∧
(∀ (i: ℕ),∀ (u v:V),i<Com.length→
(u∈ (Com.get! i))→(v∈ (Com.get! i))→(Sub.Adj u v)
→ (u∈ (Cov.get! i))∨(v∈ (Cov.get! i)))
∧
(∀ (i: ℕ),i<Cov.length→
(Cov.get! i).toFinset.card≤ κ *m)
∧
(p*Sub.edgeSet.toFinset.card+ L.Gr.edgeSet.toFinset.card≥ p*L.Gr.edgeSet.toFinset.card)
:=by
let Sub: Subgraph G:= sSup {Oi: Subgraph G| ∃ (i:ℕ), i <Ord.length∧  Oi=JClump p m κ pr h iI i Ord}

let Jmap:ℕ → Set V:= fun i=>(JClump p m κ pr h iI (i) Ord).verts
let Com: List (Set V):= List.map Jmap (List.range (Ord.length))

let Covmap:ℕ → Set V:= fun i=>(JCover iI  i Ord)
let Cov: List (Set V):= List.map Covmap (List.range (Ord.length))

have Comlen: Com.length=Ord.length:= by
  dsimp[Com]
  simp
have getCom: ∀ (i: ℕ ), i<Com.length→
  ((List.map Jmap (List.range Ord.length)).getD i default)
  =(JClump p m κ pr h iI i Ord).verts:= by
    intro i hi
    have geteq: (List.map Jmap (List.range Ord.length)).getD i default=(List.map Jmap (List.range Ord.length)).get ⟨ i, hi⟩:= by
      exact List.getD_eq_get (List.map Jmap (List.range Ord.length)) default hi
    rw[geteq]
    dsimp[Jmap]
    simp
rw[Comlen] at getCom

have Covlen: Cov.length=Ord.length:= by
  dsimp[Cov]
  simp
have getCov: ∀ (i: ℕ ), i<Cov.length→
  ((List.map Covmap (List.range Ord.length)).getD i default)
  =(JCover iI  i Ord):= by
    intro i hi
    have geteq: (List.map Covmap (List.range Ord.length)).getD i default=(List.map Covmap (List.range Ord.length)).get ⟨ i, hi⟩:= by
      exact List.getD_eq_get (List.map Covmap (List.range Ord.length)) default hi
    rw[geteq]
    dsimp[Covmap]
    simp
rw[Covlen] at getCov

use Sub
use Com
use Cov
constructor


dsimp[Sub]
intro v hv
simp at hv
dsimp[Com]
rcases hv with ⟨i, hi1, hi2 ⟩
use i
simp
rw[getCom]
constructor
exact hi1
exact hi2
exact hi1


constructor
dsimp [Com]
simp
intro i j hi hj hdiff
rw[getCom]
rw[getCom]
apply Jset_disjoint_ne
repeat assumption

constructor
dsimp[Com]
simp
intro i j u v hi hj hdiff
rw[getCom]
rw[getCom]
apply Jset_no_edges
dsimp[Sub]
repeat assumption

constructor
dsimp[Com, Cov]
simp
intro i u v hi
rw[getCom, getCov]
apply JSet_covered_by_M
dsimp[Sub]
repeat assumption

constructor
dsimp[Cov]
simp only [List.length_map, List.length_range, List.get!_eq_getD]
intro i hi
rw[getCov]
apply JCover_bound
repeat assumption

apply sum_Grs_sub_approx
repeat assumption
dsimp[Sub]
repeat assumption














def Components_cover_graph (Sub: Subgraph G) (Com: List (Set V)):=
  (∀ (v: V), v∈ Sub.verts→ ∃ (i: ℕ ),v∈ (Com.get! i) )

def Components_disjoint (Com: List (Set V)):=
  (∀ (i j: ℕ),i<Com.length→j<Com.length→i≠ j→
  (Disjoint (Com.get! i) (Com.get! j)))

def No_edges_between_components (Sub: Subgraph G) (Com: List (Set V)):=
  (∀ (i j: ℕ), ∀ (u v: V),i<Com.length→j<Com.length→ i≠ j→
  u∈ (Com.get! i)→ v∈   (Com.get! j)
  → ¬ (Sub.Adj u v))

def Components_covered_by_covers (Sub: Subgraph G) (Com Cov: List (Set V)):=
  (∀ (i: ℕ),∀ (u v:V),i<Com.length→
  (u∈ (Com.get! i))→(v∈ (Com.get! i))→(Sub.Adj u v)
  → (u∈ (Cov.get! i))∨(v∈ (Cov.get! i)))

def Covers_small (κ m: ℕ )(Cov: List (Set V)):=
  (∀ (i: ℕ),i<Cov.length→
  (Cov.get! i).toFinset.card≤ κ *m)

lemma theorem_conversion2
(L: Locally_Dense G p m h)
(Ord: List (Clump G p m κ pr h))
(decomp: Clump_Decomposition L (Ord.toFinset))
(approx: ∀ (i: ℕ ),
i≤ Ord.length→
p*(JClump p m κ pr h iI i Ord).edgeSet.toFinset.card
+
 ((Ord.get! i)).Gr.edgeSet.toFinset.card
≥
p*(Ord.get! i).Gr.edgeSet.toFinset.card
)
(narrow: Clump_family_narrow  (Ord.toFinset))
(nodup:Ord.Nodup)
:
∃(Sub: Subgraph G), ∃ (Com Cov: List (Set V)),
Components_cover_graph Sub Com
∧
Components_disjoint Com
∧
No_edges_between_components Sub Com
∧
Components_covered_by_covers Sub Com Cov
∧
Covers_small κ m Cov
∧
(p*Sub.edgeSet.toFinset.card+ L.Gr.edgeSet.toFinset.card≥ p*L.Gr.edgeSet.toFinset.card)
:=by
unfold Components_cover_graph
unfold Components_disjoint
unfold No_edges_between_components
unfold Components_covered_by_covers
unfold Covers_small


let Sub: Subgraph G:= sSup {Oi: Subgraph G| ∃ (i:ℕ), i <Ord.length∧  Oi=JClump p m κ pr h iI i Ord}

let Jmap:ℕ → Set V:= fun i=>(JClump p m κ pr h iI (i) Ord).verts
let Com: List (Set V):= List.map Jmap (List.range (Ord.length))

let Covmap:ℕ → Set V:= fun i=>(JCover iI  i Ord)
let Cov: List (Set V):= List.map Covmap (List.range (Ord.length))

have Comlen: Com.length=Ord.length:= by
  dsimp[Com]
  simp
have getCom: ∀ (i: ℕ ), i<Com.length→
  ((List.map Jmap (List.range Ord.length)).getD i default)
  =(JClump p m κ pr h iI i Ord).verts:= by
    intro i hi
    have geteq: (List.map Jmap (List.range Ord.length)).getD i default=(List.map Jmap (List.range Ord.length)).get ⟨ i, hi⟩:= by
      exact List.getD_eq_get (List.map Jmap (List.range Ord.length)) default hi
    rw[geteq]
    dsimp[Jmap]
    simp
rw[Comlen] at getCom

have Covlen: Cov.length=Ord.length:= by
  dsimp[Cov]
  simp
have getCov: ∀ (i: ℕ ), i<Cov.length→
  ((List.map Covmap (List.range Ord.length)).getD i default)
  =(JCover iI  i Ord):= by
    intro i hi
    have geteq: (List.map Covmap (List.range Ord.length)).getD i default=(List.map Covmap (List.range Ord.length)).get ⟨ i, hi⟩:= by
      exact List.getD_eq_get (List.map Covmap (List.range Ord.length)) default hi
    rw[geteq]
    dsimp[Covmap]
    simp
rw[Covlen] at getCov

use Sub
use Com
use Cov
constructor


dsimp[Sub]
intro v hv
simp at hv
dsimp[Com]
rcases hv with ⟨i, hi1, hi2 ⟩
use i
simp
rw[getCom]

exact hi2
exact hi1


constructor
dsimp [Com]
simp
intro i j hi hj hdiff
rw[getCom]
rw[getCom]
apply Jset_disjoint_ne
repeat assumption

constructor
dsimp[Com]
simp
intro i j u v hi hj hdiff
rw[getCom]
rw[getCom]
apply Jset_no_edges
dsimp[Sub]
repeat assumption

constructor
dsimp[Com, Cov]
simp
intro i u v hi
rw[getCom, getCov]
apply JSet_covered_by_M
dsimp[Sub]
repeat assumption

constructor
dsimp[Cov]
simp only [List.length_map, List.length_range, List.get!_eq_getD]
intro i hi
rw[getCov]
apply JCover_bound
repeat assumption

apply sum_Grs_sub_approx
repeat assumption
dsimp[Sub]
repeat assumption
