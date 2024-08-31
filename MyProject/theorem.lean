
import MyProject

import MyProject.wide_or_separated_gives_path
import MyProject.brooms
import MyProject.locally_dense_find

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats 100000

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

theorem version1
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
+
 ((Ord.get! i)).Gr.edgeSet.toFinset.card
≥
p*(Ord.get! i).Gr.edgeSet.toFinset.card
)
∧
Clump_family_narrow  (Ord.toFinset)
:=by

have hNoWideClumps: ¬ L_contains_wide_clump p m κ pr h G L :=by
  by_contra wideclump
  unfold L_contains_wide_clump at wideclump
  rcases wideclump with ⟨K, ⟨K_In_L, ⟨hWide1, hWide2⟩⟩⟩
  have hPath:Has_length_d_path (L.Gr) (h*m):=by
    apply Wide_clump_implies_path iI iV
    repeat assumption

  exact no_paths hPath

have nan:(Clump G p m κ pr h) :=by
  exact Inhabited.default

have hDecompositionExistence:
  ∃ (KFam: Finset (Clump G p m κ pr h)),
  Clump_Decomposition L KFam
  ∧ Clump_family_narrow KFam
  ∧ Clump_family_separated KFam:=by
    apply Clump_decomposition_of_locally_dense
    repeat assumption



rcases hDecompositionExistence with ⟨KFam, ⟨ hKFamDecomp, hKFamNarrow, hKFamSeparat⟩ ⟩

have hNonemp: KFam.Nonempty:=by
    unfold  Clump_Decomposition at hKFamDecomp
    unfold L_contained_in_clump_family   at hKFamDecomp
    rcases LNonempty with ⟨Li, hLi ⟩
    have hex: ∃ K ∈ KFam, Li ≤ K.Gr:= by
      apply hKFamDecomp.2.2
      assumption
    rcases hex with ⟨K, hK1, hK2 ⟩
    use K


have NoDenseSets: ¬ family_contains_dense_list p m κ pr h α iI KFam :=by
  by_contra hDenseSets
  have hPath:Has_length_d_path (L.Gr) (h*m):=by
    apply dense_list_implies_path iI iV
    repeat assumption
    unfold Clump_Decomposition at hKFamDecomp
    repeat assumption
    exact hKFamDecomp.2.1
    repeat assumption



  exact no_paths hPath


have OrdExistence:
  ∃ (Ord: List (Clump G p m κ pr h)),
  (Ord.toFinset= KFam)∧
  (Ord.Nodup)∧
  (clump_list_sparse_up_to_n p m κ pr h α iI (KFam.card) Ord )
  :=by
    apply Order_family
    repeat assumption

rcases OrdExistence with ⟨Ord, ⟨hOrd1, ⟨hOrd2, hOrd3⟩⟩⟩


use Ord
constructor
rw[hOrd1]
exact hKFamDecomp

constructor
intro i hi
let K:=(Ord.get! i)
have hK: K=   (Ord.get! i):=by
  exact rfl
let J:=(JClump p m κ pr h iI i Ord)
have hJ: J= JClump p m κ pr h iI i Ord:=by
  exact rfl
rw[hK.symm]
rw[hJ.symm]

have hOrdLength: Ord.length=KFam.card:=by
  rw[hOrd1.symm]
  exact (List.toFinset_card_of_nodup hOrd2).symm

rw[hOrdLength.symm] at hOrd3
apply edges_in_JClump_4 p m κ pr h α iI iSub --i Ord hOrd3 K hK J hJ
repeat assumption
calc
  α ≥ h := by
    assumption
  _≥ pr:= by
    apply gg1_ge
    repeat assumption
  _≥  gg1 p:=by
    apply gg2_gg1
    repeat assumption

repeat assumption
rw[hOrd1]
exact hKFamNarrow
/-
lemma Order_family
(KFam: Finset (Clump G p m κ pr h))
(no_dense_sets: ¬ family_contains_dense_list p m κ pr h α iI KFam  )
:
∃ (Li: List (Clump G p m κ pr h)),
(Li.toFinset= KFam)∧
(Li.Nodup)∧
(clump_list_sparse_up_to_n p m κ pr h α iI (KFam.card) Li )


lemma edges_in_JClump_4
(i: ℕ )
(Ord: List (Clump G p m κ pr h))
(Ord_Sparse: clump_list_sparse_up_to_n p m κ pr h α hI (Ord.length) Li )
(K: Clump G p m κ pr h)
(hK: K=   (Ord.get! i))
(J: Subgraph G)
(hJ: J= JClump p m κ pr h hI i Ord)
:
p*J.edgeSet.toFinset.card
+
 K.Gr.edgeSet.toFinset.card
≥
p*K.Gr.edgeSet.toFinset.card
-/
theorem version2
(L: Locally_Dense G p m h)
(LNonempty: L.H.Nonempty )
(no_paths: ¬ Has_length_d_path (L.Gr) (h*m))
:
∃ (f: V→ Set V), ∃ (Sub: Subgraph G),
(∀ (x: V), Sub.neighborSet x ⊆  f x)
∧ (∀ ( x y: V), f x ≠ f y → (Disjoint (f x) (f y)))
∧ (∀ (x: V), (f x).toFinset.card≤ (κ *m))
∧ (p*Sub.edgeSet.toFinset.card+ L.Gr.edgeSet.toFinset.card≥ p*L.Gr.edgeSet.toFinset.card)
:=by
sorry
/-
have hex:
  ∃ (Ord: List (Clump G p m κ pr h)),
  Clump_Decomposition L (Ord.toFinset)
  ∧
  (∀ (i: ℕ ),
  i≤ Ord.length→
  p*(JClump p m κ pr h iI i Ord).edgeSet.toFinset.card
  +
  ((Ord.get! i)).Gr.edgeSet.toFinset.card
  ≥
  p*(Ord.get! i).Gr.edgeSet.toFinset.card
  ):= by
    apply version1
    repeat assumption

rcases hex with ⟨Ord, hOrd1, hOrd2 ⟩

let Sub: Subgraph G:= sSup {Oi: Subgraph G| ∃ (i:ℕ), i <Ord.length∧  Oi=JClump p m κ pr h iI i Ord}
let g: V→ Set (Subgraph G):=
  fun v => {Oi: Subgraph G| ∃ (i:ℕ), i <Ord.length∧  Oi=JClump p m κ pr h iI i Ord∧  v∈ Oi.verts}
let f: V→ Set V:=
  fun v=> if hne: (g v).Nonempty    then hne.some.verts  else {v}
---------f should only take M rather than all of J
use f
use Sub
constructor
--edges stay in fv
intro v
intro y hy
dsimp [Sub] at hy
simp at hy
--dsimp [f]
by_cases case: ¬((g v).Nonempty)

/-
have hfv: f v ={v}:= by
  dsimp [f]
  simp
  intro h1
  exfalso
  exact case h1
rw[hfv]
simp-/
rcases hy with ⟨j, hKj, hKj2 ⟩
have nin: v∉ (JClump p m κ pr h iI j Ord).verts:= by
  by_contra cont
  have h2: (JClump p m κ pr h iI j Ord)∈ g v:= by
    dsimp[g]
    use j
  have h3: (g v).Nonempty:= by
    use (JClump p m κ pr h iI j Ord)
  exact case h3
exfalso
have hcon: v ∈  (JClump p m κ pr h iI j Ord).verts:= by
  exact (JClump p m κ pr h iI j Ord).edge_vert hKj2
exact nin hcon

simp at case
have hfv: f v =case.some.verts:= by
  dsimp [f]
  exact dif_pos case
rw[hfv]
sorry

constructor

sorry

constructor
-/
