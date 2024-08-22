import MyProject

import MyProject.Basic

def gg1 (b: ℕ ): ℕ := 10000 *b^4*2^b

def gg2 (b: ℕ ): ℕ := gg1 (b^4) * gg1 b*(2*b)*gg1 ( gg1 (b^4))





def GG (a b: ℕ ): Prop:=
a≥ gg1 b


@[inherit_doc] infixl:50 " ≫  " => GG

lemma gg1_1
{a b: ℕ}
(h: a ≥ gg1 b)
(bPositive: b>0)
:
a≥10000 *b^3
:= by
calc
a≥ gg1 b:= by
  exact h
_≥ 10000 *b^4*1:= by
  unfold gg1
  gcongr
  exact Nat.one_le_two_pow

_= 10000 *b^4:= by
  ring_nf
_≥10000 *b^3:= by
  gcongr
  exact bPositive
  exact Nat.le_of_ble_eq_true rfl



lemma gg1_2
{a b: ℕ}
(h: a ≥ gg1 b)
(bPositive: b>0)
:
a≥b^4
:= by
calc
a≥ gg1 b:= by
  exact h
_≥ 1 *b^4*1:= by
  unfold gg1
  gcongr
  simp
  exact Nat.one_le_two_pow
_= b^4:= by
  ring_nf

lemma gg1_3
{a b: ℕ}
(h: a ≥ gg1 b)
(bPositive: b>0)
:
a≥10000 *b^4
:= by
calc
a≥ gg1 b:= by
  exact h
_≥ 10000 *b^4*1:= by
  unfold gg1
  gcongr
  exact Nat.one_le_two_pow

_= 10000 *b^4:= by
  ring_nf


lemma gg1_ge
{a b: ℕ}
(h: a ≥ gg1 b)
(bPositive: b>0)
:
a≥  b
:= by
calc
  a≥10000 *b^3:= by apply gg1_1 h bPositive
  _=10000*b*b*b:= by ring_nf
  _≥ 1*b*1*1:=by
    gcongr
    simp
    exact bPositive
    exact bPositive
  _=b:= by
    ring_nf


lemma gg1_pos
{b: ℕ}
(bPositive: b>0)
:
gg1 b>0
:= by
calc
  gg1 b=10000 *b^4*2^b:= by
    unfold gg1
    exact rfl
  _>0:= by
    apply mul_pos
    apply mul_pos
    simp
    exact Nat.pos_pow_of_pos 4 bPositive
    exact Nat.two_pow_pos b



lemma gg1_trans
{a b c: ℕ}
(h: a ≥ gg1 b)
(h2: b ≥ gg1 c)
(bPositive: b>0)
:
a≥  gg1 c
:= by
calc
  a≥ b:= by
    apply gg1_ge
    assumption
    assumption
  _≥ gg1 c:= by
    exact h2

/-
lemma gg1_increasing
{a b c: ℕ}
(h: a ≥ gg1 b)
(bPositive: b>0)
(cPositive: c>0)
(b_le_c: b≤c)
:
a≥ gg1 c
:= by
calc
  a≥ gg1 b:= by
    exact h
  _≥ gg1 c:= by
    unfold gg1
    gcongr
    exact b_le_c
    exact Nat.le_of_lt cPositive
    exact Nat.le_of_lt cPositive-/

lemma gg2_1
{a b: ℕ}
(h: a ≥ gg2 b)
(bPositive: b>0)
:
a≥ gg1 (b^4)
:= by
calc
a≥ gg2 b:= by
  exact h
_≥ gg1 (b^4)*1*(1*1)*1:= by
  unfold gg2
  gcongr
  apply gg1_pos
  assumption
  simp
  assumption
  apply gg1_pos
  apply gg1_pos
  exact Nat.pos_pow_of_pos 4 bPositive

_= gg1 (b^4):= by
  ring_nf



lemma gg2_3
{a b: ℕ}
(h: a ≥ gg2 b)
(bPositive: b>0)
:
a≥ gg1 (gg1 (b^4))
:= by
calc
a≥ gg2 b:= by
  exact h
_≥ 1*1*(1*1)*(gg1 (gg1 (b^4))):= by
  unfold gg2
  gcongr
  apply gg1_pos
  exact Nat.pos_pow_of_pos 4 bPositive
  apply gg1_pos
  assumption
  simp
  assumption


_= (gg1 (gg1 (b^4))):= by
  ring_nf

lemma gg2_gg1
{a b: ℕ}
(h: a ≥ gg2 b)
(bPositive: b>0)
:
a≥ gg1 (b)
:= by
calc
a≥ gg2 b:= by
  exact h
_≥ 1*gg1 (b)*(1*1)*1:= by
  unfold gg2
  gcongr
  apply gg1_pos
  exact Nat.pos_pow_of_pos 4 bPositive
  simp
  assumption
  apply gg1_pos
  apply gg1_pos
  exact Nat.pos_pow_of_pos 4 bPositive
_= gg1 (b):= by
  ring_nf



lemma gg2_ge
{a b: ℕ}
(h: a ≥ gg2 b)
(bPositive: b>0)
:
a≥  b
:= by
calc
  a≥ gg1 b:= by
    apply gg2_gg1
    assumption
    assumption
  _≥ b:= by
    apply gg1_ge
    exact Nat.le_refl (gg1 b)
    assumption

lemma gg2_trans
{a b c: ℕ}
(h: a ≥ gg2 b)
(h2: b ≥ gg2 c)
(bPositive: b>0)
:
a≥  gg2 c
:= by
calc
  a≥ b:= by
    apply gg2_ge
    assumption
    assumption
  _≥ gg2 c:= by
    exact h2


lemma gg2_pos
{b: ℕ}
(bPositive: b>0)
:
gg2 b>0
:= by
have h1 :  gg2 b≥ gg2 b:= by
  exact Nat.le_refl (gg2 b)
have h2: gg2 b≥ gg1 b:= by
  apply gg2_gg1
  assumption
  assumption
calc
gg2 b≥ gg1 b:= by exact h2
_ >0:= by
  apply gg1_pos
  assumption


/-
lemma gg2_2
{a b: ℕ}
(h: a ≥ gg2 b)
(bPositive: b>0)
:
a/(2*b)≥ gg1 b
:= by
calc
a/(2*b)≥ gg2 b/(2*b):= by
  apply Nat.div_le_div_right
  exact h

_= gg1 (b ^ 4) * gg1 b := by
  unfold gg2
  refine Nat.mul_div_cancel (gg1 (b ^ 4) * gg1 b) ?H
  apply mul_pos
  simp
  assumption
_≥ 1*gg1 b:= by
  gcongr
  apply gg1_pos
  exact Nat.pos_pow_of_pos 4 bPositive
_= gg1 b:= by
  ring_nf-/
