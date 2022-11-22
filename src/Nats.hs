{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Nats where

import Base
import Data.Type.Equality

data Nat where
  Zero ∷ Nat
  Suc ∷ Nat → Nat
  deriving (Show, Eq, Ord)

-----------------------------------
-- Creating Numbers (Term Level) --
-----------------------------------

-- zero
-- >>> Zero
-- Zero

-- one
-- >>> Suc Zero
-- Suc Zero

-- two
-- >>> Suc (Suc Zero)
-- Suc (Suc Zero)

-- three
-- >>> Suc (Suc (Suc Zero))
-- Suc (Suc (Suc Zero))

---------------
-- DataKinds --
---------------

-- >>> :type Zero
-- Zero ∷ Nat

-- >>> :type Suc
-- Suc ∷ Nat → Nat

-- >>> :kind 'Suc
-- 'Suc ∷ Nat → Nat

-- >>> :kind 'Zero
-- 'Zero ∷ Nat

-- N0 is type alias with kind Nat without a data constructor.
type N0 = 'Zero

-- >>> :kind N0
-- N0 ∷ Nat

-- >>> :type N0
-- Data constructor not in scope: N0

type One = 'Suc N0

type Two = 'Suc One

-----------
-- Proof --
-----------

----------------
-- Term Level --
----------------

-- We want to prove: one + one = two!

-- For comparison.
-- Addition for Nat's (term level).
-- https://en.wikipedia.org/wiki/Peano_axioms#Addition
(+.) ∷ Nat → Nat → Nat
Zero +. b = b
(Suc a) +. b = Suc (a +. b)

infixl 5 +.

-- one + one = two
-- >>> (Suc Zero) +. (Suc Zero)
-- Suc (Suc Zero)

-- three + two = five
-- >>> Suc(Suc(Suc Zero)) +. (Suc(Suc Zero))
-- Suc (Suc (Suc (Suc (Suc Zero))))

----------------
-- Type Level --
----------------

-- Type families can be seen as functions on types!

-- Addition (type level) for Nat kinds.
type family (a ∷ Nat) :+: (b ∷ Nat) ∷ Nat where
  'Zero :+: b = b
  'Suc a :+: b = 'Suc (a :+: b)

-- >>> :kind (:+:)
-- (:+:) ∷ Nat → Nat → Nat

-- one + one = two
-- >>> :kind! One :+: One
-- One :+: One ∷ Nat
-- = 'Suc ('Suc N0)

-- Proof that one + one = two!
onePlusOne ∷ (One :+: One) :~: Two
onePlusOne = Refl

-- GHC error: "Couldn't match type ‘n’ with ‘n :+: 'Zero’"
-- nPlusZero1 ∷ (n :+: 'Zero) :~: n
-- nPlusZero1 = Refl

-- :+: pattern matches on the left argument, but now we have 'Zero on the right.
-- Hence the expected way to proceed is to pattern match on `n`.
-- Unfortunately, we cannot pattern match on types directly so we need to figure something out.

----------------
-- Singletons --
----------------

-- One type, one term.
-- If you know the type, you know the term and vice versa.

-- SNat = Singleton Nat
data SNat (n ∷ Nat) where
  SZero ∷ SNat 'Zero
  SSuc ∷ SNat n → SNat ('Suc n)

-- >>> :kind SNat
-- SNat ∷ Nat → Type

-----------------------------------
-- Creating Numbers (Type Level) --
-----------------------------------

-- For any type `n` of kind Nat, the type `SNat n` has exactly one term ⇒ SNat is a singleton type.

-- SNat has the same structure as a Nat, but it is INDEXED by a Nat on the type level.
-- Note that the `n` in the first line is NOT a term of type Nat.
-- Instead, `n` is a type variable of kind Nat.
-- With the help of GADTs, we can use the promoted constructors 'Zero and 'Suc to create the desired link between terms and types.

-- >>> :kind! SZero
-- SZero ∷ SNat 'Zero
-- = 'SZero

-- >>> :kind! (SSuc SZero)
-- (SSuc SZero) ∷ SNat ('Suc 'Zero)
-- = 'SSuc 'SZero

-- >>> :kind! (SSuc (SSuc SZero))
-- (SSuc (SSuc SZero)) ∷ SNat ('Suc ('Suc 'Zero))
-- = 'SSuc ('SSuc 'SZero)

-------------------------------
-- Pattern Matching on Types --
-------------------------------

-- We can use the singleton type SNat to pattern match on types of kind Nat.

-- n + 0 = n
-- nPlusZero ∷ SNat n → (n :+: 'Zero) :~: n
-- nPlusZero SZero = _
-- nPlusZero (SSuc n) = _

-- ⇒
nPlusZero ∷ SNat n → (n :+: 'Zero) :~: n
nPlusZero SZero = Refl
nPlusZero (SSuc n) = cong (nPlusZero n)

---------------------
-- Theorem Proving --
---------------------

-- We want to prove some theorem.
someTheoremm ∷ SNat a → SNat b → (a :+: b) :+: 'Zero :~: (a :+: b)
someTheoremm a b = nPlusZero (a .+. b)

-- It is clear that the strategy should be to instantiate the n in the lemma nPlusZero as a :+: b.
-- But then we should provide an argument of type `SNat (a :+: b)`.
-- We can achieve that by implementing addition for the type SNat.

-- addition term level (for SNats)
(.+.) ∷ SNat a → SNat b → SNat (a :+: b)
(.+.) SZero b = b
(.+.) (SSuc n) b = SSuc (n .+. b)

infixl 9 .+.

-- multiplication term level (for SNats)
(.*.) ∷ SNat a → SNat b → SNat (a :*: b)
(.*.) SZero _ = SZero
(.*.) (SSuc a) b = b .+. (a .*. b)

infixl 9 .*.

-- exponentiation term level (for SNats)
(.^.) ∷ SNat a → SNat b → SNat (a :^: b)
(.^.) _ SZero = SSuc SZero
(.^.) a (SSuc b) = a .*. (a .^. b)

infixl 9 .^.

-- multiplication (type level)
type family (a ∷ Nat) :*: (b ∷ Nat) ∷ Nat where
  'Zero :*: b = 'Zero
  'Suc a :*: b = b :+: (a :*: b)

-- exponentiation (type level)
type family (a ∷ Nat) :^: (b ∷ Nat) ∷ Nat where
  a :^: 'Zero = 'Suc 'Zero
  a :^: 'Suc b = a :*: (a :^: b)

---------------
-- Exercises --
---------------

--  1. plusSucR ∷ SNat a → SNat b → (a :+: 'Suc b) :~: 'Suc (a :+: b)
plusSucR ∷ SNat a → SNat b → (a :+: 'Suc b) :~: 'Suc (a :+: b)
plusSucR SZero _  = Refl
plusSucR (SSuc a) b  = cong (plusSucR a b)

--  2. plusAssoc ∷ SNat a → SNat b → SNat c → (a :+: b) :+: c :~: a :+: (b :+: c)
plusAssoc ∷ SNat a → SNat b → SNat c → (a :+: b) :+: c :~: a :+: (b :+: c)
plusAssoc SZero _ _ = Refl
plusAssoc (SSuc a) b c = cong (plusAssoc a b c)

--  3. plusCommut ∷ SNat a → SNat b → (a :+: b) :~: (b :+: a)
-- plusCommut ∷ SNat a → SNat b → (a :+: b) :~: (b :+: a)
-- plusCommut SZero b = sym (plusZeroR b)
-- plusCommut (SSuc a) b = _1 `trans` _2
--   where
--     fu1 ∷ (a' :+: b') :~: (b' :+: a')
--     fu1 = plusCommut a b ∷ _3

-- _ ∷ (b :+: 'Suc a) :~: 'Suc (a :+: b)

-- plusCommut ∷ ∀ a b. SNat a → SNat b → (a :+: b) :~: (b :+: a)
-- plusCommut SZero b = sym (plusZeroR b)
-- plusCommut (SSuc (pa ∷ SNat pa)) b = cong indh `trans` sym (plusSucR b pa)
--   where
--     indh ∷ (pa :+: b) :~: (b :+: pa)
--     indh = plusCommut pa b

-- >>> :type trans
-- trans
--   ∷ ∀ k (a ∷ k) (b ∷ k) (c ∷ k).
--      (a :~: b)
--    → (b :~: c)
--    →  a :~: c

-- _ ∷ ('Suc (n :+: b) :~: 'Suc (b :+: n))
--   → ('Suc (b :+: n) :~: (b :+: 'Suc n))
--   →  'Suc (n :+: b) :~: (b :+: 'Suc n)

-- >>> :type plusCommut (SSuc SZero) (SSuc (SSuc SZero))
-- plusCommut (SSuc SZero) (SSuc (SSuc SZero)) ∷ 'Suc ('Suc ('Suc 'Zero)) :~: 'Suc ('Suc ('Suc 'Zero))

plusZeroR ∷ SNat a → (a :+: 'Zero) :~: a
plusZeroR SZero = Refl
plusZeroR (SSuc a) = cong (plusZeroR a)

-- _ ∷ (a :+: 'Suc b) :~: (b :+: 'Suc a)
-- _ ∷ (a :+: 'Suc b) :~: ('Suc a :+: b)

--  4. prodZeroL ∷ SNat n → 'Zero :*: n :~: 'Zero
--  5. prodZeroR ∷ SNat a → (a :*: 'Zero) :~: 'Zero
--  6. prodOneL ∷ SNat sn → (One :*: sn) :~: sn
--  7. prodOneR ∷ SNat sn → (sn :*: One) :~: sn
--  8. prodSucL ∷ SNat a → SNat b → ('Suc a :*: b) :~: b :+: (a :*: b)
--  9. prodSucR ∷ SNat a → SNat b → (a :*: 'Suc b) :~: a :+: (a :*: b)
-- 10. prodDistribR ∷ SNat a → SNat b → SNat c → (a :+: b) :*: c :~: (a :*: c) :+: (b :*: c)
-- 11. prodDistribL ∷ SNat a → SNat b → SNat c → a :*: (b :+: c) :~: (a :*: b) :+: (a :*: c)
-- 12. prodAssoc ∷ SNat a → SNat b → SNat c → (a :*: b) :*: c :~: a :*: (b :*: c)
-- 13. prodCommut ∷ SNat a → SNat b → (a :*: b) :~: (b :*: a)
-- 14. powerZero ∷ a :^: 'Zero :~: One
-- 15. powerOne ∷ SNat a → a :^: One :~: a
-- 16. prodPower ∷ SNat a → SNat b → SNat c → (a :^: b) :*: (a :^: c) :~: a :^: (b :+: c)
-- 17. powerProd ∷ SNat a → SNat b → SNat c → (a :^: c) :*: (b :^: c) :~: (a :*: b) :^: c

{-

plusZeroL ∷ ('Zero :+: b) :~: b
plusZeroL = Refl

plusZeroR ∷ SNat sn → (sn :+: 'Zero) :~: sn
plusZeroR SZero = Refl
plusZeroR (SSuc (n ∷ SNat n)) = congSuc (plusZeroR n)

plusSucL ∷ SNat a → SNat b → ('Suc a :+: b) :~: 'Suc (a :+: b)
plusSucL _ _ = Refl

plusSucR ∷ ∀ a b. SNat a → SNat b → (a :+: 'Suc b) :~: 'Suc (a :+: b)
plusSucR SZero _ = Refl
plusSucR (SSuc (pa ∷ SNat pa)) b = congSuc indh
  where
    indh ∷ (pa :+: 'Suc b) :~: 'Suc (pa :+: b)
    indh = plusSucR pa b

plusEqL ∷ SNat k → a :~: b → k :+: a :~: k :+: b
plusEqL SZero Refl = Refl
plusEqL (SSuc n) p = congSuc (plusEqL n p)

plusEqR ∷ ∀ k a b. SNat k → SNat a → a :~: b → a :+: k :~: b :+: k
plusEqR _k _a Refl = Refl

plusAssoc ∷ ∀ a b c. SNat a → SNat b → SNat c → (a :+: b) :+: c :~: a :+: (b :+: c)
plusAssoc SZero _ _ = Refl
plusAssoc (SSuc (pa ∷ SNat pa)) b c = congSuc (plusAssoc pa b c)

plusCommut ∷ ∀ a b. SNat a → SNat b → (a :+: b) :~: (b :+: a)
plusCommut SZero b = sym (plusZeroR b)
plusCommut (SSuc (pa ∷ SNat pa)) b = congSuc indh `trans` sym (plusSucR b pa)
  where
    indh ∷ (pa :+: b) :~: (b :+: pa)
    indh = plusCommut pa b

plusTransL ∷ SNat b → c :~: a :+: b → a :~: a' → c :~: a' :+: b
plusTransL _ Refl Refl = Refl

plusTransR ∷ SNat a → c :~: a :+: b → b :~: b' → c :~: a :+: b'
plusTransR _ Refl Refl = Refl

prodZeroL ∷ SNat n → 'Zero :*: n :~: 'Zero
prodZeroL _n = Refl

prodZeroR ∷ SNat sn → (sn :*: 'Zero) :~: 'Zero
prodZeroR SZero = Refl
prodZeroR (SSuc (n ∷ SNat n)) = indh
  where
    indh ∷ (n :*: 'Zero) :~: 'Zero
    indh = prodZeroR n

prodOneL ∷ SNat sn → (One :*: sn) :~: sn
prodOneL = plusZeroR

prodOneR ∷ SNat sn → (sn :*: One) :~: sn
prodOneR SZero = Refl
prodOneR (SSuc (n ∷ SNat n)) = congSuc indh
  where
    indh = prodOneR n

prodSucL ∷ ∀ a b. SNat a → SNat b → ('Suc a :*: b) :~: b :+: (a :*: b)
prodSucL _ _ = Refl

prodSucR ∷ ∀ a b. SNat a → SNat b → (a :*: 'Suc b) :~: a :+: (a :*: b)
prodSucR SZero _ = Refl
prodSucR (SSuc (n ∷ SNat n)) b = congSuc s3
  where
    indh ∷ (n :*: 'Suc b) :~: (n :+: (n :*: b))
    indh = prodSucR n b
    nb = n .*. b
    s1 ∷ (b :+: (n :*: 'Suc b)) :~: ((b :+: n) :+: (n :*: b))
    s1 =
      plusEqL b indh
        `trans` sym (plusAssoc b n nb)
    s2 ∷ (b :+: (n :*: 'Suc b)) :~: ((n :+: b) :+: (n :*: b))
    s2 = plusTransL nb s1 (plusCommut b n)
    s3 ∷ (b :+: (n :*: 'Suc b)) :~: (n :+: (b :+: (n :*: b)))
    s3 = s2 `trans` plusAssoc n b nb

prodTransL ∷ SNat b → c :~: a :*: b → a :~: a' → c :~: a' :*: b
prodTransL _ Refl Refl = Refl

prodTransR ∷ SNat a → c :~: a :*: b → b :~: b' → c :~: a :*: b'
prodTransR _ Refl Refl = Refl

prodDistribR ∷
  ∀ a b c.
  SNat a →
  SNat b →
  SNat c →
  (a :+: b) :*: c :~: (a :*: c) :+: (b :*: c)
prodDistribR SZero _b _c = Refl
prodDistribR (SSuc (n ∷ SNat n)) b c = s1 `trans` sym (plusAssoc c nc bc)
  where
    indh ∷ ((n :+: b) :*: c) :~: ((n :*: c) :+: (b :*: c))
    indh = prodDistribR n b c
    s1 ∷ c :+: ((n :+: b) :*: c) :~: c :+: ((n :*: c) :+: (b :*: c))
    s1 = plusEqL c indh
    nc ∷ SNat (n :*: c)
    nc = n .*. c
    bc ∷ SNat (b :*: c)
    bc = b .*. c

prodDistribL ∷
  ∀ a b c.
  SNat a →
  SNat b →
  SNat c →
  a :*: (b :+: c) :~: (a :*: b) :+: (a :*: c)
prodDistribL SZero _b _c = Refl
prodDistribL (SSuc (n ∷ SNat n)) b c = s6
  where
    nb = n .*. b
    nc = n .*. c
    indh ∷ (n :*: (b :+: c)) :~: ((n :*: b) :+: (n :*: c))
    s1 ∷ ((b :+: c) :+: (n :*: (b :+: c))) :~: ((b :+: c) :+: ((n :*: b) :+: (n :*: c)))
    s2 ∷ ((b :+: c) :+: (n :*: (b :+: c))) :~: (b :+: (c :+: ((n :*: b) :+: (n :*: c))))
    s3 ∷ ((b :+: c) :+: (n :*: (b :+: c))) :~: (b :+: ((c :+: (n :*: b)) :+: (n :*: c)))
    s4 ∷ ((b :+: c) :+: (n :*: (b :+: c))) :~: (b :+: (((n :*: b) :+: c) :+: (n :*: c)))
    s5 ∷ ((b :+: c) :+: (n :*: (b :+: c))) :~: (b :+: ((n :*: b) :+: (c :+: (n :*: c))))
    s6 ∷ ((b :+: c) :+: (n :*: (b :+: c))) :~: ((b :+: (n :*: b)) :+: (c :+: (n :*: c)))
    indh = prodDistribL n b c
    s1 = plusEqL (b .+. c) indh
    s2 = s1 `trans` plusAssoc b c (nb .+. nc)
    s3 = plusTransR b s2 (sym (plusAssoc c nb nc))
    s4 = plusTransR b s3 (plusEqR nc (c .+. nb) (plusCommut c nb))
    s5 = plusTransR b s4 (plusAssoc nb c nc)
    s6 = s5 `trans` sym (plusAssoc b nb (c .+. nc))

prodAssoc ∷ ∀ a b c. SNat a → SNat b → SNat c → (a :*: b) :*: c :~: a :*: (b :*: c)
prodAssoc SZero _b _c = Refl
prodAssoc (SSuc (n ∷ SNat n)) b c = plusEqL bc indh `transL` sym (prodDistribR b nb c)
  where
    indh ∷ ((n :*: b) :*: c) :~: (n :*: (b :*: c))
    indh = prodAssoc n b c
    bc ∷ SNat (b :*: c)
    bc = b .*. c
    nb ∷ SNat (n :*: b)
    nb = n .*. b

prodCommut ∷ ∀ a b. SNat a → SNat b → (a :*: b) :~: (b :*: a)
prodCommut SZero b = sym (prodZeroR b)
prodCommut (SSuc (n ∷ SNat n)) b = s2
  where
    indh ∷ (n :*: b) :~: (b :*: n)
    indh = prodCommut n b
    s1 ∷ (b :+: (n :*: b)) :~: b :+: (b :*: n)
    s1 = plusEqL b indh
    s2 ∷ (b :+: (n :*: b)) :~: (b :*: 'Suc n)
    s2 = s1 `trans` sym (prodSucR b n)

prodEqL ∷ SNat k → a :~: b → k :*: a :~: k :*: b
prodEqL SZero Refl = Refl
prodEqL (SSuc (_ ∷ SNat n)) Refl = Refl

prodEqR ∷ SNat k → a :~: b → a :*: k :~: b :*: k
prodEqR SZero Refl = Refl
prodEqR (SSuc (_ ∷ SNat n)) Refl = Refl

powerZero ∷ a :^: 'Zero :~: One
powerZero = Refl

powerOne ∷ SNat a → a :^: One :~: a
powerOne SZero = Refl
powerOne (SSuc (n ∷ SNat n)) = congSuc (prodOneR n)

powerTransExp ∷ SNat a → c :~: a :^: b → b :~: b' → c :~: a :^: b'
powerTransExp _ Refl Refl = Refl

prodPower ∷
  ∀ a b c.
  SNat a →
  SNat b →
  SNat c →
  (a :^: b) :*: (a :^: c) :~: a :^: (b :+: c)
prodPower a SZero c = plusZeroR (a .^. c)
prodPower a (SSuc (n ∷ SNat n)) c = s2
  where
    indh ∷ ((a :^: n) :*: (a :^: c)) :~: (a :^: (n :+: c))
    indh = prodPower a n c
    s1 ∷ (a :*: ((a :^: n) :*: (a :^: c))) :~: (a :*: (a :^: (n :+: c)))
    s2 ∷ ((a :*: (a :^: n)) :*: (a :^: c)) :~: (a :*: (a :^: (n :+: c)))
    s1 = prodEqL a indh
    s2 = s1 `transL` sym (prodAssoc a (a .^. n) (a .^. c))

powerProd ∷
  ∀ a b c.
  SNat a →
  SNat b →
  SNat c →
  (a :^: c) :*: (b :^: c) :~: (a :*: b) :^: c
powerProd _ _ SZero = Refl
powerProd a b (SSuc (n ∷ SNat n)) = s6
  where
    an = a .^. n
    bn = b .^. n
    indh = powerProd a b n
    indh ∷ ((a :^: n) :*: (b :^: n)) :~: ((a :*: b) :^: n)
    s1 ∷ ((a :*: b) :*: ((a :^: n) :*: (b :^: n))) :~: ((a :*: b) :*: ((a :*: b) :^: n))
    s2 ∷ (a :*: (b :*: ((a :^: n) :*: (b :^: n)))) :~: ((a :*: b) :*: ((a :*: b) :^: n))
    s3 ∷ (a :*: ((b :*: (a :^: n)) :*: (b :^: n))) :~: ((a :*: b) :*: ((a :*: b) :^: n))
    s4 ∷ (a :*: (((a :^: n) :*: b) :*: (b :^: n))) :~: ((a :*: b) :*: ((a :*: b) :^: n))
    s5 ∷ (a :*: ((a :^: n) :*: (b :*: (b :^: n)))) :~: ((a :*: b) :*: ((a :*: b) :^: n))
    s6 ∷ ((a :*: (a :^: n)) :*: (b :*: (b :^: n))) :~: ((a :*: b) :*: ((a :*: b) :^: n))
    s1 = prodEqL (a .*. b) indh
    s2 = s1 `transL` prodAssoc a b (an .*. bn)
    s3 = sym (prodTransR a (sym s2) (sym (prodAssoc b an bn)))
    s4 = sym (prodTransR a (sym s3) (prodEqR bn (prodCommut b an)))
    s5 = sym (prodTransR a (sym s4) (prodAssoc an b bn))
    s6 = s5 `transL` sym (prodAssoc a an (b .*. bn))

powerPower ∷
  ∀ a b c.
  SNat a →
  SNat b →
  SNat c →
  (a :^: b) :^: c :~: a :^: (b :*: c)
powerPower a b SZero = powerTransExp a (sym powerZero) (sym (prodZeroR b))
powerPower a b (SSuc (n ∷ SNat n)) = s3
  where
    indh = powerPower a b n
    indh ∷ ((a :^: b) :^: n) :~: (a :^: (b :*: n))
    s1 ∷ ((a :^: b) :*: ((a :^: b) :^: n)) :~: (a :^: b) :*: (a :^: (b :*: n))
    s2 ∷ ((a :^: b) :*: ((a :^: b) :^: n)) :~: (a :^: (b :+: (b :*: n)))
    s3 ∷ ((a :^: b) :*: ((a :^: b) :^: n)) :~: (a :^: (b :*: 'Suc n))
    s1 = prodEqL (a .^. b) indh
    s2 = s1 `trans` prodPower a b (b .*. n)
    s3 = powerTransExp a s2 (sym (prodSucR b n))

-}
