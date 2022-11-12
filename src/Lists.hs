module Lists where

import Base
import Data.Kind
import Data.Type.Equality
import Nats

data HList (l ∷ [*]) ∷ * where
  HNil ∷ HList '[]
  HCons ∷ t → HList l → HList (t ': l)

type family Length (l ∷ [*]) ∷ Nat where
  Length '[] = 'Zero
  Length (_' : r) = 'Suc (Length r)

type family (a ∷ [*]) :++: (b ∷ [*]) ∷ [*] where
  '[] :++: b = b
  (a : as) :++: b = a : (as :++: b)

type family Reverse (a ∷ [*]) ∷ [*] where
  Reverse '[] = '[]
  Reverse (a : as) = Reverse as :++: '[a]

type family Filter (f ∷ * → Bool) (l ∷ [*]) ∷ [*] where
  Filter f '[] = '[]
  Filter f (x : xs) = ConsIf (f x) x (Filter f xs)

type family ConsIf (c ∷ Bool) (x ∷ *) (xs ∷ [*]) ∷ [*] where
  ConsIf 'True x xs = x ': xs
  ConsIf _ x xs = xs

type family (a ∷ Nat) :⇐: (b ∷ Nat) ∷ Bool where
  a :⇐: a = 'True
  'Suc a :⇐: a = 'False
  a :⇐: 'Suc b = a :⇐: b

type family (a ∷ Nat) :!⇐: (b ∷ Nat) ∷ * where
  a :!⇐: a = *
  a :!⇐: 'Suc b = a :!⇐: b

data SUnit ∷ * → * where
  SUnit ∷ SUnit *

(.++.) ∷ HList a → HList b → HList (a :++: b)
HNil .++. b = b
HCons t l .++. b = HCons t (l .++. b)

infixl 9 .++.

(.:.) ∷ t → HList a → HList (t ': a)
t .:. l = HCons t l

infixl 9 .:.

slist ∷ t → HList '[t]
slist t = HCons t HNil

slength ∷ HList l → SNat (Length l)
slength HNil = SZero
slength (HCons _ t) = SSuc (slength t)

sreverse ∷ HList l → HList (Reverse l)
sreverse HNil = HNil
sreverse (HCons a as) = sreverse as .++. slist a

concatNilL ∷ '[] :++: a :~: a
concatNilL = Refl

concatNilR ∷ HList a → a :++: '[] :~: a
concatNilR HNil = Refl
concatNilR (HCons _ l) = cong (concatNilR l)

lengthEq ∷ a :~: a' → Length a :~: Length a'
lengthEq Refl = Refl

lengthCons ∷ HList a → Length (t ': a) :~: 'Suc (Length a)
lengthCons _ = Refl

reverseEq ∷ a :~: a' → Reverse a :~: Reverse a'
reverseEq Refl = Refl

concatEqR ∷ HList x → a :~: b → a :++: x :~: b :++: x
concatEqR x Refl = Refl

concatEqL ∷ HList x → a :~: b → x :++: a :~: x :++: b
concatEqL x Refl = Refl

lengthConcat ∷ HList a → HList b → Length a :+: Length b :~: Length (a :++: b)
lengthConcat HNil b = Refl
lengthConcat (HCons _ t) b = congSuc indh
  where
    indh = lengthConcat t b

concatAssoc ∷
  ∀ a b c.
  HList a →
  HList b →
  HList c →
  (a :++: b) :++: c :~: a :++: (b :++: c)
concatAssoc HNil b c = Refl
concatAssoc (HCons (t ∷ t) (l ∷ HList l)) b c = cong indh
  where
    indh ∷ ((l :++: b) :++: c) :~: (l :++: (b :++: c))
    indh = concatAssoc l b c

lengthConcatCommut ∷
  ∀ a b.
  HList a →
  HList b →
  Length (a :++: b) :~: Length (b :++: a)
lengthConcatCommut HNil b = lengthEq (sym (concatNilR b))
lengthConcatCommut (HCons (t ∷ t) (l ∷ HList l)) b = s5
  where
    indh ∷ Length (l :++: b) :~: Length (b :++: l)
    indh = lengthConcatCommut l b
    s1 ∷ Length (l :++: b) :~: Length b :+: Length l
    s2 ∷ 'Suc (Length (l :++: b)) :~: 'Suc (Length b :+: Length l)
    s3 ∷ 'Suc (Length (l :++: b)) :~: (Length b :+: 'Suc (Length l))
    s4 ∷ 'Suc (Length (l :++: b)) :~: (Length b :+: Length ('[t] :++: l))
    s5 ∷ 'Suc (Length (l :++: b)) :~: Length (b :++: ('[t] :++: l))
    s1 = indh `trans` sym (lengthConcat b l)
    s2 = congSuc s1
    s3 = s2 `trans` sym (plusSucR (slength b) (slength l))
    s4 = plusTransR (slength b) s3 (sym (lengthCons l))
    s5 = s4 `trans` lengthConcat b (t .:. l)

lengthReverse ∷ HList a → Length (Reverse a) :~: Length a
lengthReverse HNil = Refl
lengthReverse (HCons (t ∷ t) (l ∷ HList l)) = s3
  where
    indh ∷ Length (Reverse l) :~: Length l
    indh = lengthReverse l
    s1 ∷ 'Suc (Length (Reverse l)) :~: 'Suc (Length l)
    s2 ∷ Length ('[t] :++: Reverse l) :~: 'Suc (Length l)
    s3 ∷ Length (Reverse l :++: '[t]) :~: 'Suc (Length l)
    s1 = congSuc indh
    s2 = s1 `transL` sym (lengthCons (sreverse l))
    s3 = s2 `transL` lengthConcatCommut (slist t) (sreverse l)

concatReverse ∷
  ∀ a b.
  HList a →
  HList b →
  Reverse a :++: Reverse b :~: Reverse (b :++: a)
concatReverse a HNil = concatNilR (sreverse a)
concatReverse a (HCons (t ∷ t) (l ∷ HList l)) = s2
  where
    indh = concatReverse a l
    indh ∷ (Reverse a :++: Reverse l) :~: Reverse (l :++: a)
    s1 ∷ (Reverse a :++: Reverse l) :++: '[t] :~: Reverse (l :++: a) :++: '[t]
    s2 ∷ Reverse a :++: (Reverse l :++: '[t]) :~: Reverse (l :++: a) :++: '[t]
    s1 = concatEqR (slist t) indh
    s2 = s1 `transL` concatAssoc (sreverse a) (sreverse l) (slist t)

consReverse ∷ ∀ a t. HList a → t ': Reverse a :~: Reverse (a :++: '[t])
consReverse HNil = Refl
consReverse (HCons (x ∷ x) (l ∷ HList l)) = s1
  where
    indh ∷ (t ': Reverse l) :~: Reverse (l :++: '[t])
    indh = consReverse l
    s1 ∷ (t ': Reverse l) :++: '[x] :~: Reverse (l :++: '[t]) :++: '[x]
    s1 = concatEqR (slist x) indh

reverseReverse ∷ ∀ a. HList a → Reverse (Reverse a) :~: a
reverseReverse HNil = Refl
reverseReverse (HCons (t ∷ t) (l ∷ HList l)) = s2
  where
    indh ∷ Reverse (Reverse l) :~: l
    indh = reverseReverse l
    s1 ∷ t ': Reverse (Reverse l) :~: t ': l
    s2 ∷ Reverse (Reverse l :++: '[t]) :~: (t ': l)
    s1 = concatEqL (slist t) indh
    s2 = s1 `transL` consReverse (sreverse l)
