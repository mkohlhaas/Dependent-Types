module Base where

import Data.Kind
import Data.Type.Equality

data Equal a b where
  Witness ∷ (a ~ b) ⇒ Equal a b

-- But we use :~: from Data.Type.Equality.
-- Refl ≌ Reflexivity
-- >>> :info :~:
-- type role (:~:) nominal nominal
-- type (:~:) ∷ ∀ k. k → k → *
-- data (:~:) a b where
--   Refl ∷ ∀ k (a ∷ k). (:~:) a a
--   	-- Defined in ‘Data.Type.Equality’

--------------
-- Symmetry --
--------------

-- >>> :type sym
-- sym ∷ ∀ k (a ∷ k) (b ∷ k). (a :~: b) → b :~: a

sym1 ∷ ∀ (a ∷ Type) (b ∷ Type). (a :~: b) → (b :~: a)
sym1 Refl = Refl

-- >>> :type sym1
-- sym1 ∷ (a :~: b) → b :~: a

-- >>> :type Refl
-- Refl ∷ ∀ k (a ∷ k). a :~: a

sym2 ∷ ∀ (k ∷ Type) (a ∷ k) (b ∷ k). (a :~: b) → (b :~: a)
sym2 = sym3

-- >>> :type sym2
-- sym2 ∷ ∀ k (a ∷ k) (b ∷ k). (a :~: b) → b :~: a

sym3 ∷ ∀ (k ∷ Type) (x ∷ k) (y ∷ k). (x :~: y) → (y :~: x)
sym3 = sym2

-- >>> :type sym3
-- sym3 ∷ ∀ k (x ∷ k) (y ∷ k). (x :~: y) → y :~: x

------------------
-- Transitivity --
------------------

-- trans from Data.Type.Equality
-- >>> :type trans
-- trans
--   ∷ ∀ k (a ∷ k) (b ∷ k) (c ∷ k).
--      (a :~: b) → (b :~: c) → a :~: c

trans1 ∷ a :~: b → b :~: c → a :~: c
trans1 Refl Refl = Refl

transL ∷ a :~: b → a :~: c → b :~: c
transL Refl Refl = Refl

-- >>> :type transL
-- transL
--   ∷ ∀ k (a ∷ k) (b ∷ k) (c ∷ k).
--      (a :~: b) → (a :~: c) → b :~: c

----------------
-- Relexivity --
----------------

refl1 ∷ a :~: a → a :~: a
refl1 Refl = Refl

----------------

-- :~: is symmetric, transitive and reflexive ⇒  :~: is an equivalence relation.

-- GHC doesn't complain but this "proof" will never finish. So it's NOT a proof.
anyProof ∷ a
anyProof = anyProof

-- does not finish
-- >>> anyProof

cong ∷ a :~: b → f a :~: f b
cong Refl = Refl

-- and so on ...
cong1 ∷ a :~: b → f g a :~: f g b
cong1 Refl = Refl
