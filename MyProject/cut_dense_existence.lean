import MyProject
import MyProject.interedges_auxiliary
--import MyProject.cut_dense_basics
  --import MyProject.SimpleGraph

open Classical
open Finset
open scoped BigOperators

namespace SimpleGraph


set_option maxHeartbeats  170000

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
--variable (iI:Inhabited (Clump G p m κ pr h))
variable (iV:Inhabited V)
variable (iSub:Inhabited (Subgraph G))
--variable (iSP:Inhabited (SubgraphPath_implicit   G) )






noncomputable def  v ( B: Finset V):ℚ  :=B.card
noncomputable def  e (H: Subgraph G) ( B: Finset V):ℚ  :=(H.induce B).edgeSet.toFinset.card
noncomputable def  vv (H: Subgraph G):ℚ  := H.verts.toFinset.card
noncomputable def ee (H: Subgraph G):ℚ := H.edgeSet.toFinset.card
--noncomputable def den (H: Subgraph G):ℚ := (e H)/(v H)^2--(H.edgeSet.toFinset.card: ℚ )/(H.verts.toFinset.card:ℚ )^2
noncomputable def eBip (H: Subgraph G) (A B: Finset V):ℚ :=
  (Rel.interedges H.Adj A B).card


theorem cut_dense_negation_AB_Sum
(H: Subgraph G)
(A B: Finset V)
(disj: Disjoint A B)
(part: H.verts.toFinset= A ∪ B)
--(inter: p*(Rel.interedges H.Adj A B).card≤ 4*A.card*B.card)
:
v A + v B=vv H
:=by
unfold v
unfold vv
--simp
symm
apply nat_rat_add --A.card B.card (filter (fun x ↦ x ∈ H.verts) univ).card ?heq).symm
rw[part]
exact card_disjoint_union disj



lemma rat_nat_ineq
(a b: ℕ )
(hab: a= b)
:
(a: ℚ )= (b: ℚ )
:= by
exact congrArg Nat.cast hab



theorem cut_dense_negation_interedges0
(H: Subgraph G)
(A B: Finset V)
(inter: p*(Rel.interedges H.Adj A B).card≤ 4*A.card*B.card)
:
p* eBip H A B≤  4*v A * v B
:=by
unfold eBip
unfold v
have h1: ((p*(Rel.interedges H.Adj A B).card:ℕ ): ℚ )≤ ((4*A.card*B.card:ℕ  ):ℚ ):= by
  apply nat_le_rat
  exact inter
simp at h1
exact h1

theorem cut_dense_negation_interedges
(H: Subgraph G)
(A B: Finset V)
--(disj: Disjoint A B)
(part: H.verts.toFinset= A ∪ B)
--(inter: p*(Rel.interedges H.Adj A B).card≤ 4*A.card*B.card)
:
e H A + e H B+ 2*eBip H A B≥ ee H
:=by
unfold e
unfold ee
unfold eBip
congr
have h1:
  ((H.induce A).edgeSet.toFinset.card: ℚ) + ((H.induce B).edgeSet.toFinset.card: ℚ ) + (2*(Rel.interedges H.Adj A B).card: ℚ )
  =((((H.induce A).edgeSet.toFinset.card + (H.induce B).edgeSet.toFinset.card + 2*(Rel.interedges H.Adj A B).card): ℕ ): ℚ )
  := by
    simp
rw[h1]
apply nat_le_rat
let f: (V× V) → Sym2 V:=(fun x=>  Sym2.mk x)

calc
  (H.induce ↑A).edgeSet.toFinset.card + (H.induce ↑B).edgeSet.toFinset.card + 2*(Rel.interedges H.Adj A B).card
  =(H.induce ↑A).edgeSet.toFinset.card + (H.induce ↑B).edgeSet.toFinset.card + (Rel.interedges H.Adj A B).card+(Rel.interedges H.Adj A B).card:=by
    ring_nf
  _=(H.induce ↑A).edgeSet.toFinset.card + (H.induce ↑B).edgeSet.toFinset.card + (Rel.interedges H.Adj A B).card+(Rel.interedges H.Adj B A).card:=by
    congr 1
    exact Rel.card_interedges_comm (fun ⦃x y⦄ a ↦ id (Subgraph.adj_symm H a)) A B
  _≥  (H.induce ↑A).edgeSet.toFinset.card + (H.induce ↑B).edgeSet.toFinset.card + ((Finset.image f) (Rel.interedges H.Adj A B) ).card+((Finset.image f) (Rel.interedges H.Adj B A) ).card
  := by

    gcongr
    exact card_image_le
    exact card_image_le
  _≥ _--((H.induce ↑A).edgeSet.toFinset∪  (H.induce ↑B).edgeSet.toFinset∪ (Finset.image f (Rel.interedges H.Adj A B)) ).card
  :=by
    --have h2: _:= by
    exact card_union_4 (H.induce ↑A).edgeSet.toFinset (H.induce ↑B).edgeSet.toFinset (Finset.image f (Rel.interedges H.Adj A B)) ((Finset.image f) (Rel.interedges H.Adj B A) )
    --simp at h2
    --simp
    --exact h2
  _≥  H.edgeSet.toFinset.card:= by
    gcongr
    intro e  he
    have h4: ∃ (a b: V), e= s(a,b):= by
      exact Sym2_to_tuple e
    rcases h4 with ⟨a, b, hab⟩
    rw[hab]
    rw[hab] at he
    simp
    simp at he
    unfold Rel.interedges
    simp
    dsimp [f]
    simp

    have hain: a∈ H.verts.toFinset:=by simp; exact H.edge_vert he
    have hbin: b∈ H.verts.toFinset:=by simp; exact H.edge_vert (id (Subgraph.adj_symm H he))
    rw[part] at hain
    rw[part] at hbin
    simp at hain
    simp at hbin
    rcases hain with casea|casea
    rcases hbin with caseb|caseb
    aesop
    aesop
    rcases hbin with caseb|caseb
    aesop
    aesop








theorem cut_dense_negation
(H: Subgraph G)
(AS BS: Finset V)
(hUnion:H.verts.toFinset= AS ∪ BS)
(hNotCut: p * (Rel.interedges H.Adj AS BS).card < AS.card * BS.card)
(hAbigger: AS.card≥ 5)
:∃(A B: Finset V),
(Disjoint A B) ∧ (H.verts.toFinset= A ∪ B)
∧
(p*(Rel.interedges H.Adj A B).card≤  16*(A.card)*(B.card))
∧ A.card>0
∧
B.card>0
:=by--- can make this inequality strict

have ASnonemp:  AS.card>0:= by
  by_contra cont
  simp at cont
  have h1: p * (Rel.interedges H.Adj AS BS).card <0:=by
    calc
      p * (Rel.interedges H.Adj AS BS).card < AS.card * BS.card:= by
        exact hNotCut
      _= 0*BS.card:= by
        congr
        exact card_eq_zero.mpr cont
      _=0:= by
        ring_nf
  have h2: ¬ ( p * (Rel.interedges H.Adj AS BS).card <0):= by
    simp
  exact h2 h1

have BSnonemp:  BS.card>0:= by
  by_contra cont
  simp at cont
  have h1: p * (Rel.interedges H.Adj AS BS).card <0:=by
    calc
      p * (Rel.interedges H.Adj AS BS).card < AS.card * BS.card:= by
        exact hNotCut
      _= AS.card*0:= by
        congr
        exact card_eq_zero.mpr cont
      _=0:= by
        ring_nf
  have h2: ¬ ( p * (Rel.interedges H.Adj AS BS).card <0):= by
    simp
  exact h2 h1

let I: Finset V:= AS∩ BS
let a: ℕ := I.card/2
let b: ℕ := I.card-a





have exAI: ∃ (AI: Finset V), AI ⊆ I ∧ AI.card=a:= by
  refine exists_smaller_set I a ?h₁
  dsimp [a]
  exact Nat.div_le_self I.card 2

rcases exAI with ⟨AI, hAI1, hAI2⟩
let BI: Finset V:= I\AI
have hBI: BI.card=b:= by
  rw[card_sdiff hAI1]
  dsimp [b]
  rw[hAI2]
have hBI2: BI⊆ I:= by
  dsimp [BI]
  exact sdiff_subset I AI

let A': Finset V:= AS\I ∪ AI
let B': Finset V:= BS\I ∪ BI

have A'Nonemp: A'.card>0:= by
  dsimp [A']
  by_cases case: a>0
  calc
    (AS \ I ∪ AI).card≥  AI.card:=by
      gcongr
      exact subset_union_right (AS \ I) AI
    _>0:= by rw[hAI2]; exact case


  --dsimp[a] at case
  simp at case
  calc
  (AS \ I ∪ AI).card≥ (AS \ I).card:= by
    gcongr
    exact subset_union_left (AS \ I) AI
  _≥ (AS).card-I.card:= by
    exact le_card_sdiff I AS
  _≥ 5- (2*a+2):= by
    gcongr

    dsimp[a]
    refine div_assoc_3 ?hcd.cPos
    exact Nat.zero_lt_two
  _=3:= by
    rw[case]
    ring_nf
  _> 0:= by exact Nat.zero_lt_succ 2




have B'Nonemp: B'.card>0:= by

  by_cases case: b>0
  dsimp [B']
  calc
    (BS \ I ∪ BI).card≥  BI.card:=by
      gcongr
      exact subset_union_right (BS \ I) BI
    _>0:= by rw[hBI]; exact case


  dsimp[b] at case
  simp at case
  dsimp[a] at case
  have h:I.card=0:= by exact Nat.eq_zero_of_le_half case
  have hIemp: I=∅ := by exact card_eq_zero.mp h
  have hh:B'=BS:= by
    dsimp [B']
    dsimp[BI]
    rw[hIemp]
    simp
  rw[hh]
  exact BSnonemp


use A'
use B'
constructor



dsimp[A', B']
dsimp [I]
simp
constructor
constructor
exact disjoint_sdiff_sdiff
have h1: Disjoint I (BS \ AS):= by
  dsimp[I]
  refine disjoint_left.mpr ?_
  intro a ha
  simp
  simp at ha
  intro hb
  exact ha.1
exact disjoint_of_subset_left hAI1 h1

constructor
have h1: Disjoint (AS \ BS) I:= by
  dsimp[I]
  refine disjoint_right.mpr ?_
  intro a ha
  simp
  simp at ha
  intro hb
  exact ha.2
exact Disjoint.symm (disjoint_of_subset_left hBI2 (id (Disjoint.symm h1)))

dsimp [BI]
exact disjoint_sdiff

constructor

dsimp[A', B']
dsimp [BI]
symm
calc
  AS \ I ∪ AI ∪ (BS \ I ∪ I \ AI)
  =AS \ I ∪  (BS \ I) ∪ (AI ∪ I \ AI):= by
    simp
    congr 1
    rw[union_comm]
    simp
    congr 1
    exact union_comm I AI
  _=AS \ I ∪  (BS \ I) ∪ ( I ):= by
    congr
    simp
    exact hAI1
  _= H.verts.toFinset:= by
    rw[hUnion]
    simp
    dsimp [I]
    simp
    ext a
    simp
    constructor
    intro ha
    aesop
    intro ha
    by_cases h:a∈ BS
    right
    left
    exact h
    aesop

have h8: Disjoint (AS\ I) I:= by exact Disjoint.symm disjoint_sdiff
have h9: Disjoint (BS\ I) I:= by exact Disjoint.symm disjoint_sdiff
have h10: BI⊆ I:= by dsimp[BI]; exact hBI2

have hAcc: 4*A'.card≥ AS.card:= by
  --dsimp [A']
  calc
    4*A'.card= 2*A'.card+2*A'.card:= by
      ring_nf
    _≥ 2*A'.card+2*1:= by
      gcongr
      exact A'Nonemp
    _=2 * (AS \ I ∪ AI).card+2:= by
      dsimp [A']


    _= 2*((AS\ I).card + AI.card)+2:= by
      congr
      refine card_disjoint_union ?_
      exact Disjoint.symm (disjoint_of_subset_left hAI1 (id (Disjoint.symm h8)))

    _=  2*((AS\ I).card + (I).card/2)+2:= by
      rw[hAI2]
    _=  2*(AS\ I).card + (2*((I).card/2)+2):= by
      ring_nf
    _≥   2*(AS\ I).card + 2*(I).card/2:= by
      gcongr
      apply div_assoc_le2
      exact Nat.zero_lt_two
    _=  2*(AS\ I).card + I.card:= by
      congr
      refine (Nat.eq_div_of_mul_eq_right ?_ rfl).symm
      exact Ne.symm (Nat.zero_ne_add_one 1)
    _≥ 1*(AS\ I).card + I.card:= by
      gcongr
      exact NeZero.one_le
    _=(AS\ I).card + I.card:= by
      ring_nf
    _= AS.card:= by
      congr
      refine card_sdiff_add_card_eq_card ?h
      dsimp[I]
      exact inter_subset_left AS BS


have hBcc: 4*B'.card≥ BS.card:= by

  calc
    4*B'.card= 2*B'.card+2*B'.card:= by
      ring_nf
    _≥ 2*B'.card+2*1:= by
      gcongr
      exact B'Nonemp
    _=2 * (BS \ I ∪ BI).card+2:= by
      dsimp [B']

    _= 2*((BS\ I).card + BI.card)+2:= by
      congr
      refine card_disjoint_union ?_
      apply disjoint_of_subset_right
      exact h10
      exact h9

    _≥   2*((BS\ I).card + (I).card/2)+2:= by
      gcongr
      rw[hBI]
      dsimp[b, a]
      exact minus_half_halves_ge I.card

    _=  2*(BS\ I).card + (2*((I).card/2)+2):= by
      ring_nf
    _≥   2*(BS\ I).card + 2*(I).card/2:= by
      gcongr
      apply div_assoc_le2
      exact Nat.zero_lt_two
    _=  2*(BS\ I).card + I.card:= by
      congr
      refine (Nat.eq_div_of_mul_eq_right ?_ rfl).symm
      exact Ne.symm (Nat.zero_ne_add_one 1)
    _≥ 1*(BS\ I).card + I.card:= by
      gcongr
      exact NeZero.one_le
    _=(BS\ I).card + I.card:= by
      ring_nf
    _= BS.card:= by
      congr
      refine card_sdiff_add_card_eq_card ?h
      dsimp[I]
      exact inter_subset_right AS BS


have h82:A'⊆ AS:=by
  dsimp [A']
  have h3: I⊆ AS:= by
    dsimp [I]
    exact inter_subset_left AS BS
  have h2: AI⊆ AS:= by
    dsimp [I] at hAI1
    exact fun ⦃a⦄ a_1 ↦ h3 (hAI1 a_1)
  have h7: AS \ I⊆ AS:= by
    exact sdiff_subset AS I
  exact union_subset h7 h2

have h92:B'⊆ BS:=by
  dsimp [B']
  have h3: I⊆ BS:= by
    dsimp [I]
    exact inter_subset_right AS BS
  have h2: BI⊆ BS:= by
    --dsimp [I] at hBI1
    exact fun ⦃a⦄ a_1 ↦ h3 (hBI2 a_1)
  have h7: BS \ I⊆ BS:= by
    exact sdiff_subset BS I
  exact union_subset h7 h2
constructor
calc
  p * (Rel.interedges H.Adj A' B').card
  ≤
  p * (Rel.interedges H.Adj AS BS).card
  := by
    gcongr
    exact interedges_subset G h82 h92
  _≤ AS.card*BS.card:= by exact Nat.le_of_succ_le hNotCut
  _≤   (4 * A'.card) * (4*B'.card):= by
    gcongr
    repeat assumption
  _= 16*A'.card*B'.card:= by
    ring_nf



exact ⟨A'Nonemp, B'Nonemp ⟩


theorem cut_dense_negation2
(H: Subgraph G)

(hlarge: H.verts.toFinset.card≥ 20)
(not_cut_dense : ¬cut_dense G H p)
:∃(A B: Finset V),
(Disjoint A B) ∧ (H.verts.toFinset= A ∪ B)
∧
(p*(Rel.interedges H.Adj A B).card≤  16*(A.card)*(B.card))
∧
A.card>0
∧
B.card>0
:=by
unfold cut_dense at not_cut_dense
simp at not_cut_dense
rcases not_cut_dense with ⟨AS, BS, hUnion, hNotCut⟩

by_cases case: AS.card≥ 5
apply cut_dense_negation H AS BS hUnion hNotCut case
repeat assumption

simp at case
have Bcard: BS.card≥ 5:= by
  by_contra cont
  simp at cont
  have h1: 20< 10:= by
    calc
      20≤ H.verts.toFinset.card:= by
        exact hlarge
      _≤  AS.card+BS.card:= by
        rw[hUnion]
        exact card_union_le AS BS
      _< 5+5:= by
        gcongr

      _=10:= by
        ring_nf
  have h2: ¬ (20<10):= by
    simp
  exact h2 h1

apply cut_dense_negation H BS AS
rw[hUnion]
exact union_comm AS BS
calc
  p * (Rel.interedges H.Adj BS AS).card
  =p * (Rel.interedges H.Adj AS BS).card:= by
    congr 1
    exact Rel.card_interedges_comm (fun ⦃x y⦄ a ↦ id (Subgraph.adj_symm H a)) BS AS
  _< AS.card * BS.card:= by
    exact hNotCut
  _=BS.card * AS.card:= by
    exact Nat.mul_comm AS.card BS.card

exact Bcard





theorem cut_dense_negationRat
(H: Subgraph G)
(hlarge: H.verts.toFinset.card≥ 20)
(not_cut_dense : ¬cut_dense G H p)
:∃(A B: Finset V),
(Disjoint A B) ∧ (H.verts.toFinset= A ∪ B)
∧ (vv H= v A+v B)
∧
(p*eBip H A B≤  16*(v A)*(v B))
∧
v A>0
∧
v B>0
:=by
have hex:_:= by exact cut_dense_negation2 H hlarge not_cut_dense
rcases hex with ⟨A, B, h1, h2, h3, h4⟩
use A
use B
constructor
exact h1
constructor
exact h2
constructor
exact (cut_dense_negation_AB_Sum H A B h1 h2).symm
dsimp [eBip]
dsimp [v]
have h2: (((p * (Rel.interedges H.Adj A B).card):ℕ ):ℚ)  ≤ ((16 * A.card * B.card:ℕ ):ℚ ):=by
  apply nat_le_rat
  exact h3
simp at h2
simp
constructor
exact h2

exact h4

end SimpleGraph

lemma small_inequality
(a b h A B H p: ℚ )
(pPositive: p>0)
(notcutdense: a+b+p*A*B/4≥ h)
(cardsum: A+B=H)
(Hdensity: h/H^2≥ p)
(b_small: b≤ B^2)
(Bsmall: B≤ p*H/4)
(Bpositive: B>0)
(Apositive: A>0)
(Hpositive: H>0)
(hnonneg: h≥ 0)
(HlargerthanA: H≥ A)
:
a/A^2≥ (h/H^2)*(H/A)
:= by

have h1: a≥ h*A/H:= by
  calc
    a≥ h-b-p*A*B/4:= by
      linarith
    _≥ h-B^2-p*A*B/4:= by
      gcongr
    _= h-B*B-p*A*B/4:= by
      ring_nf
    _≥ h-B*(p*H/4)-p*A*B/4:= by
      gcongr
    _≥ h-B*(p*H/4)-p*H*B/4:= by
      gcongr

    _=  h-p*B*H/2:= by
      linarith
    _≥  h-(h/H^2)*B*H/2:= by
      gcongr

    _= h-(h/H)*B/2:= by
      congr 1
      field_simp
      linarith
    _=(h*A/H)*(H/A-  B/(2*A)):= by
      field_simp
      linarith
    _= (h*A/H)*(H-B/2)/A:=by
      field_simp
      linarith
    _= (h*A/H)*(H-B/2)/(H-B):=by
      congr
      linarith
    _= (h*A/H)*((H-B/2)/(H-B)):= by
      ring_nf
    _≥  (h*A/H)*(1):=by
      gcongr
      refine (one_le_div ?h.hb).mpr ?h.a
      calc
        H - B=A:= by
          linarith
        _>0:= by
          exact Apositive
      gcongr
      refine half_le_self ?h.a.h.a
      exact SimpleGraph.gt_implies_gte_rational B 0 Bpositive
    _=h*A/H:= by
      ring_nf

calc
a/A^2
≥ (h*A/H)/A^2:= by
  gcongr
_= (h/H^2)*(H/A):= by
  field_simp
  linarith



lemma mult_accross
(x y c: ℚ  )
(h:x/y<c)
(ypos: y>0)
: x<c*y:= by
exact (div_lt_iff ypos).mp h

lemma mult_accross_ge
(x y c: ℚ  )
(h:x/y≥ c)
(ypos: y>0)
: x≥ c*y:= by
exact (le_div_iff ypos).mp h

/-lemma cancel_left
(x y c: ℚ  )
(h:c*x≥ c*y)
(ypos: c>0)
: x≥ y:= by
field_simp at h-/
/-by_contra con
simp at con
have h1: c*x<c*y:= by
  exact (mul_lt_mul_left ypos).mpr con
have ne: ¬ (c*x≥ c*y):= by
  exact Rat.not_le.mpr h1
exact ne h
-/
lemma big_inequality
(a b h A B H p: ℚ )
(pPositive: p>0)
(notcutdense: a+b+ε*p *A*B≥ h)
(cardsum: A+B=H)
(Hdensity: h/H^2≥ p)

(BleH: B≤ H)
(AleH: A≤ H)
(Bpositive: B>0)
(Apositive: A>0)
(Hpositive: H>0)
(epos: ε>0)
:
a/A^2≥ (h/H^2)*(H/A)*(1-ε *B/A)
∨
b/B^2≥ (h/H^2)*(H/B)*(1-ε *A/B)

:= by
by_contra cont
simp at cont
let ⟨x,y ⟩:= cont

have B2pos:B^2>0:= by exact sq_pos_of_pos Bpositive
have a2pos:A^2>0:= by exact sq_pos_of_pos Apositive
have H2pos:H^2>0:= by exact sq_pos_of_pos Hpositive


have hbb:  b   < h / H ^ 2 * (H / B) * (1 - ε * A / B)*B^2:=by
  exact mult_accross b (B ^ 2) (h / H ^ 2 * (H / B) * (1 - ε * A / B)) y B2pos

have haa:  a < h / H ^ 2 * (H / A) * (1 - ε * B / A)*A^2:=by
  exact mult_accross a (A ^ 2) (h / H ^ 2 * (H / A) * (1 - ε * B / A)) x a2pos

have h3:h-ε *p*A*B< h-ε*h := by
  calc
    h-ε *p*A*B
    ≤ a+b:= by
      linarith
    _< (h / H ^ 2 * (H / A) * (1 - ε * B / A)*A^2)+ (h / H ^ 2 * (H / B) * (1 - ε * A / B)*B^2):=by
      gcongr
    _= (h / H   * (1 - ε * B / A)*A)+ (h / H   * (1 - ε * A / B)*B):=by
      field_simp
      linarith
    _= (h / H   * ((1 - ε * B / A)*A))+ (h / H   * ((1 - ε * A / B)*B)):=by
      ring_nf
    _= (h / H   * (A - A*ε * B/A ))+ (h / H   * (B - B*ε * A/B )):=by
      ring_nf
    _= (h/H)*(A-ε *A+B-ε *B):= by
      field_simp
      ring_nf

    _= (h/H)*(A+B)*(1-ε):= by
      field_simp
      linarith
    _= (h/H)*(H)*(1-ε):= by
      rw[cardsum]
    _= h*(1-ε ):=by
      field_simp

    _=h-ε*h := by
      ring_nf

have h5: ε * (p * A * B) >  ε * h:= by
  simp
  linarith

field_simp at h5

have h7: ¬ (h≥  p * H^2):= by
  simp
  calc
    h< p * A * B:= by exact h5
    _≤ p*H*H:= by
      gcongr
    _= p*H^2:= by
      ring_nf

--have h6:  p * A * B >   h:= by
--  apply?
field_simp at Hdensity
have h8: h≥  p * H^2:= by
  apply mult_accross_ge
  exact Hdensity
  exact H2pos




exact h7 h8
 