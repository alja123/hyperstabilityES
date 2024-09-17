--import MyProject

import hyperstabilityES.lemmas.Basic
set_option linter.unusedVariables false


@[irreducible] def gg1 (b: ℕ ): ℕ := 10000 *b^4*4^(b^5)*(b ^ 16 * 75557863725914323419136)*( b ^ (2 * (100 * (5 * b^5)).factorial))

@[irreducible] def gg2 (b: ℕ ): ℕ := gg1 (b^4) * gg1 b*(2*b)*gg1 ( gg1 (b^4))*b ^ (10 * (100 * (gg1 b) ).factorial)*gg1 (b*2) * (b ^ (10 * (100 * (gg1 b)).factorial) * b ^ (10 * (100 * (gg1 b)).factorial))* (gg1 b*b^6)





def GG (a b: ℕ ): Prop:=
a≥ gg1 b


--@[inherit_doc] infixl:50 " ≫  " => GG

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
_≥ 10000 *b^4*1*(1^(16)*1)*1:= by
  unfold gg1
  gcongr
  apply Nat.one_le_pow'
  assumption
  simp
  apply Nat.one_le_pow
  exact bPositive



_= 10000 *b^4:= by
  ring_nf
_≥10000 *b^3:= by
  gcongr
  exact bPositive
  exact Nat.le_of_ble_eq_true rfl



lemma gg1_7
{a b: ℕ}
(h: a ≥ gg1 b)
(bPositive: b>0)
:
a≥(16* b ^ (2 * (100 * (5 * b^5)).factorial))
:= by
calc
  a≥ gg1 b:= by
    exact h
  _≥ 10000 *1^4*1*(1^(16)*1)*b ^ (2 * (100 * (5 * b^5)).factorial):= by
    unfold gg1
    gcongr
    exact bPositive
    apply Nat.one_le_pow'
    assumption
    simp
  _= 10000 *b ^ (2 * (100 * (5 * b^5)).factorial):= by
    ring_nf
  _≥ 16 *b ^ (2 * (100 * (5 * b^5)).factorial):= by
    gcongr
    simp
  _=_:= by ring_nf



lemma gg1_4
{a b: ℕ}
(h: a ≥ gg1 b)
(bPositive: b>0)
:
a≥(b ^ 16 * 75557863725914323419136)
:= by
calc
a≥ gg1 b:= by
  exact h
_≥ 1 *1^4*1*(b ^ 16 * 75557863725914323419136)*1:= by
  unfold gg1
  gcongr
  simp
  assumption
  apply Nat.one_le_pow'
  apply Nat.one_le_pow
  exact bPositive


_= (b ^ 16 * 75557863725914323419136):= by
  ring_nf

lemma gg1_6
{a b: ℕ}
(h: a ≥ gg1 b)
(bPositive: b>0)
:
a≥(10000*b ^ 5 )
:= by
calc
  a≥ b ^ 16 * 75557863725914323419136:= by
    apply gg1_4
    exact h
    exact bPositive
  _≥ (10000*b ^ 5 ):= by
    nth_rewrite 1 [mul_comm]
    gcongr
    simp
    exact bPositive
    simp

lemma gg1_5
{a b: ℕ}
(h: a ≥ gg1 b)
(bPositive: b>0)
:
a≥b*4^(b*b*b*b*b)
:= by
calc
a≥ gg1 b:= by
  exact h
_≥ 1 *b^1*4^(b^5)*(1^(16)*1)*1:= by
  unfold gg1
  gcongr
  simp
  assumption
  simp
  assumption
  simp
  apply Nat.one_le_pow
  exact bPositive
_= _:= by
  ring_nf

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
_≥ 1 *b^4*1*(1^(16)*1)*1:= by
  unfold gg1
  gcongr
  simp
  apply Nat.one_le_pow'
  assumption
  simp
  apply Nat.one_le_pow
  exact bPositive
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
_≥ 10000 *b^4*1*(1^(16)*1)*1:= by
  unfold gg1
  gcongr
  apply Nat.one_le_pow'
  assumption
  simp
  apply Nat.one_le_pow
  exact bPositive

_= 10000 *b^4:= by
  ring_nf


lemma gg1_large
{b: ℕ}
(bPositive: b>0)
:
gg1 b≥10000
:= by
have h1: gg1 b≥ gg1 b:= by
  exact Nat.le_refl (gg1 b)
calc
gg1 b≥ gg1 b:= by
  exact Nat.le_refl (gg1 b)
_≥ 10000 *b^3:= by
  apply gg1_1 h1
  repeat assumption

_≥ 10000 *1^3:= by
  gcongr
  assumption
_=10000:= by
  ring_nf

lemma gg1_large2
{a b: ℕ}
(bPositive: b>0)
(hab: a≥ gg1 b)
:
a≥10000
:= by
calc
a≥ gg1 b:= by
  exact hab
_≥ 10000:= by
  apply gg1_large
  assumption


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
  gg1 b≥ 10000 *b^3:= by
    apply gg1_1
    exact Nat.le_refl (gg1 b)
    assumption
  _>0:= by
    apply mul_pos
    simp
    exact Nat.pos_pow_of_pos 3 bPositive




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

lemma gg2_0
{a b: ℕ}
(h: a ≥ gg2 b)
(bPositive: b>0)
:
a≥ gg1 (b^4) * gg1 b*(2*b)*gg1 ( gg1 (b^4))*b ^ (10 * (100 * (gg1 b) ).factorial)*gg1 (b*2)
:= by
calc
  a≥ _:= by exact h
  _≥gg1 (b^4) * gg1 b*(2*b)*gg1 ( gg1 (b^4))*b ^ (10 * (100 * (gg1 b) ).factorial)*gg1 (b*2)*1*(1*1):= by
    unfold gg2
    gcongr
    rw [@Nat.succ_le_iff]
    apply mul_pos
    refine Nat.pos_pow_of_pos (10 * (100 * gg1 b).factorial) ?bc.ha.h
    assumption
    refine Nat.pos_pow_of_pos (10 * (100 * gg1 b).factorial) ?bc.ha.h
    apply gg1_pos
    exact bPositive
    rw [@Nat.succ_le_iff]
    apply Nat.pos_pow_of_pos
    exact bPositive


  _= _ :=by ring_nf
lemma gg2_1
{a b: ℕ}
(h: a ≥ gg2 b)
(bPositive: b>0)
:
a≥ gg1 (b^4)
:= by
calc
a
≥ gg1 (b^4) * gg1 b*(2*b)*gg1 ( gg1 (b^4))*b ^ (10 * (100 * (gg1 b) ).factorial)*gg1 (b*2):= by
  apply gg2_0
  repeat assumption
_≥ gg1 (b^4)*1*(1*1)*1*1*1:= by
  --unfold gg2
  gcongr
  apply gg1_pos
  assumption
  simp
  assumption
  apply gg1_pos
  apply gg1_pos
  exact Nat.pos_pow_of_pos 4 bPositive
  exact Nat.one_le_pow (10 * (100 * gg1 b).factorial) b bPositive
  apply gg1_pos
  apply mul_pos
  assumption
  simp
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
a≥ gg1 (b^4) * gg1 b*(2*b)*gg1 ( gg1 (b^4))*b ^ (10 * (100 * (gg1 b) ).factorial)*gg1 (b*2):= by
  apply gg2_0
  repeat assumption

_≥ 1*1*(1*1)*(gg1 (gg1 (b^4)))*1*1:= by
  --unfold gg2
  gcongr
  apply gg1_pos
  exact Nat.pos_pow_of_pos 4 bPositive
  apply gg1_pos
  assumption
  simp
  assumption
  exact Nat.one_le_pow (10 * (100 * gg1 b).factorial) b bPositive
  apply gg1_pos
  apply mul_pos
  assumption
  simp
_= gg1 (gg1 (b^4)):= by
  ring_nf


lemma gg2_4
{a b: ℕ}
(h: a ≥ gg2 b)
(bPositive: b>0)
:
a≥ (b ^ (10 * (100 * (gg1 b) ).factorial))
:= by
calc
a≥ gg1 (b^4) * gg1 b*(2*b)*gg1 ( gg1 (b^4))*b ^ (10 * (100 * (gg1 b) ).factorial)*gg1 (b*2):= by
  apply gg2_0
  repeat assumption
_≥ 1*1*(1*1)*1*(b ^ (10 * (100 * (gg1 b) ).factorial))*1:= by
  gcongr
  apply gg1_pos
  exact Nat.pos_pow_of_pos 4 bPositive
  apply gg1_pos
  assumption
  simp
  assumption
  apply gg1_pos
  apply gg1_pos
  exact Nat.pos_pow_of_pos 4 bPositive
  apply gg1_pos
  apply mul_pos
  assumption
  simp
_= (b ^ (10 * (100 * (gg1 b) ).factorial)):= by
  ring_nf


lemma gg2_5
{a b: ℕ}
(h: a ≥ gg2 b)
(bPositive: b>0)
:
a≥ gg1 (b*2)
:= by
calc
a≥ gg1 (b^4) * gg1 b*(2*b)*gg1 ( gg1 (b^4))*b ^ (10 * (100 * (gg1 b) ).factorial)*gg1 (b*2):= by
  apply gg2_0
  repeat assumption
_≥ 1*1*(1*1)*1*1*gg1 (b*2):= by
  gcongr
  apply gg1_pos
  exact Nat.pos_pow_of_pos 4 bPositive
  apply gg1_pos
  assumption
  simp
  assumption
  apply gg1_pos
  apply gg1_pos
  exact Nat.pos_pow_of_pos 4 bPositive
  exact Nat.one_le_pow (10 * (100 * gg1 b).factorial) b bPositive

_= gg1 (b*2):= by
  ring_nf


lemma gg2_gg1
{a b: ℕ}
(h: a ≥ gg2 b)
(bPositive: b>0)
:
a≥ gg1 (b)
:= by
calc
a≥ gg1 (b^4) * gg1 b*(2*b)*gg1 ( gg1 (b^4))*b ^ (10 * (100 * (gg1 b) ).factorial)*gg1 (b*2):= by
  apply gg2_0
  repeat assumption
_≥ 1*gg1 (b)*(1*1)*1*1*1:= by
  gcongr
  apply gg1_pos
  exact Nat.pos_pow_of_pos 4 bPositive
  simp
  assumption
  apply gg1_pos
  apply gg1_pos
  exact Nat.pos_pow_of_pos 4 bPositive
  exact Nat.one_le_pow (10 * (100 * gg1 b).factorial) b bPositive
  apply gg1_pos
  apply mul_pos
  assumption
  simp
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


lemma gg2_6
{a b: ℕ}
(h: a ≥ gg2 b)
(bPositive: b>0)
:
a≥ (b ^ (10 * (100 * (gg1 b)).factorial) * b ^ (10 * (100 * (gg1 b)).factorial))
:= by

calc
  a≥ gg2 b:= by exact h
  _≥ 1*(b ^ (10 * (100 * (gg1 b)).factorial) * b ^ (10 * (100 * (gg1 b)).factorial))*(1*1):= by
    unfold gg2
    gcongr
    rw  [@Nat.succ_le_iff]
    repeat apply mul_pos
    apply gg1_pos
    exact Nat.pos_pow_of_pos 4 bPositive
    apply gg1_pos
    exact bPositive
    apply mul_pos
    simp
    exact bPositive
    apply gg1_pos
    apply gg1_pos
    exact Nat.pos_pow_of_pos 4 bPositive
    apply Nat.pos_pow_of_pos
    exact bPositive
    apply gg1_pos
    apply mul_pos
    exact bPositive
    simp




    apply gg1_pos
    assumption
    apply Nat.pos_pow_of_pos
    assumption

    --
  _= _:= by ring_nf




lemma gg2_7
{a b: ℕ}
(h: a ≥ gg2 b)
(bPositive: b>0)
:
a≥ gg1 b^2* b^6*10000:=by
calc
a≥ gg2 b:= by exact h
_≥ gg1 (b^4) * gg1 b*(1*1)*1*1*1 * (1)* (gg1 b*b^6):= by
  unfold gg2
  gcongr
  simp
  exact bPositive
  apply gg1_pos
  apply gg1_pos
  apply Nat.pos_pow_of_pos
  exact bPositive
  apply Nat.pos_pow_of_pos
  exact bPositive
  apply gg1_pos
  apply mul_pos
  exact bPositive
  simp
  rw  [@Nat.succ_le_iff]
  apply mul_pos
  apply Nat.pos_pow_of_pos
  exact bPositive
  apply Nat.pos_pow_of_pos
  exact bPositive

_≥ 10000 * gg1 b*(1*1)*1*1*1 * (1)* (gg1 b*b^6):= by
  gcongr
  apply gg1_large
  apply Nat.pos_pow_of_pos
  exact bPositive



  --

_= _:= by ring_nf
