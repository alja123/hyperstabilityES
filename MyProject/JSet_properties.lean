import MyProject.J_bound
open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 150000

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
  calc
      κ ≥ h*4^(h*h*h):= by
        apply gg1_5
        repeat assumption
      _≥ h* 4^(pr*pr*h):= by
        gcongr h*?_
        sorry
        
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
