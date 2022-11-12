module Base where

import Data.Kind
import Data.Type.Equality

cong ∷ a :~: b → f a :~: f b
cong Refl = Refl

transL ∷ a :~: b → a :~: c → c :~: b
transL Refl Refl = Refl

sym' ∷ ∀ (x ∷ Type) (y ∷ *). (x :~: y) → (y :~: x)
sym' Refl = Refl

sym2 ∷ ∀ (k ∷ Type) (x ∷ k) (y ∷ k). (x :~: y) → (y :~: x)
sym2 = sym3

sym3 ∷ ∀ (k ∷ *) (x ∷ k) (y ∷ k). (x :~: y) → (y :~: x)
sym3 = sym2
