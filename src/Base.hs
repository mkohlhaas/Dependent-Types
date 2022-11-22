{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Base where

import Control.Category ((>>>), (<<<))
import Data.Kind ()
import Data.Type.Equality (apply, sym, trans, type (:~:)(..) )

data Equal a b where
  Same ∷ (a ~ b) ⇒ Equal a b

-- >>> :type Same
-- Same ∷ ∀ k (b ∷ k). Equal b b

-- >>> :kind Equal
-- Equal ∷ k → k → Type

-- Instead Equal we use (:~:) from Data.Type.Equality.
-- >>> :info :~:
-- type role (:~:) nominal nominal
-- type (:~:) ∷ ∀ k. k → k → Type
-- data (:~:) a b where
--   Refl ∷ ∀ k (a ∷ k). (:~:) a a

-- Refl ≌ Reflexivity

--------------
-- Strategy --
--------------

-- Write the proposition as a type and try to find a term for it.
-- If such term exists, it is obviouis that the proposition is true and thus we accept the term as a proof!

----------------
-- Relexivity --
----------------

-- by definition
refl1 ∷ a :~: a → a :~: a
refl1 Refl = Refl

--------------
-- Symmetry --
--------------

-- >>> :type sym
-- sym ∷ ∀ k (a ∷ k) (b ∷ k). (a :~: b) → b :~: a

sym1 ∷ a :~: b → b :~: a
sym1 Refl = Refl

------------------
-- Transitivity --
------------------

-- trans from Data.Type.Equality
-- >>> :type trans
-- trans
--   ∷ ∀ k (a ∷ k) (b ∷ k) (c ∷ k).
--      (a :~: b) → (b :~: c) → a :~: c

-- Note!!!
-- (:~:) is also a Category, so you can use (>>>) and (>>>) for trans!

-- >>> :type (>>>)
-- (>>>)
--   ∷ ∀ k (cat ∷ k → k → Type) (a ∷ k) (b ∷ k) (c ∷ k).
--      Category cat ⇒
--      cat a b → cat b c → cat a c

-- translates to:
-- a :~: b → b :~: c → a :~: c

-- >>> :type (<<<)
-- (<<<)
--   ∷ ∀ k (cat ∷ k → k → Type) (b ∷ k) (c ∷ k) (a ∷ k).
--      Category cat ⇒
--      cat b c → cat a b → cat a c

-- translates to:
-- b :~: c → a :~: b → a :~: c

trans1 ∷ a :~: b → b :~: c → a :~: c
trans1 Refl Refl = Refl

transL ∷ a :~: b → a :~: c → b :~: c
transL Refl Refl = Refl

-- >>> :type transL
-- transL
--   ∷ ∀ k (a ∷ k) (b ∷ k) (c ∷ k).
--      (a :~: b) → (a :~: c) → b :~: c

--------------------------
-- Equivalence Relation --
--------------------------

-- :~: is reflexive, symmetric and transitive ⇒ (:~:) is an equivalence relation.

-----------------
-- Termination --
-----------------

-- GHC doesn't complain but this "proof" will never finish. So it's NOT a proof.
anyProof ∷ a
anyProof = anyProof

-- just hangs forever
-- >>> anyProof

----------------
-- Congruency --
----------------

cong ∷ a :~: b → f a :~: f b
cong = apply Refl

-- and so on ...
cong1 ∷ a :~: b → f g a :~: f g b
cong1 = apply Refl

-- handwritten code
-- cong ∷ a :~: b → f a :~: f b
-- cong Refl = Refl

-- and so on ...
-- cong1 ∷ a :~: b → f g a :~: f g b
-- cong1 Refl = Refl
