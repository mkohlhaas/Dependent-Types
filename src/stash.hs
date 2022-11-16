--  1. plusSucR ∷ ∀ a b. SNat a → SNat b → (a :+: 'Suc b) :~: 'Suc (a :+: b)
-- plusSucR ∷ ∀ a b. SNat a → SNat b → (a :+: 'Suc b) :~: 'Suc (a :+: b)
-- plusSucR SZero SZero = Refl
-- plusSucR SZero (SSuc n) = Refl
-- plusSucR (SSuc n) SZero = cong (plusSucR n SZero)
-- plusSucR (SSuc n) (SSuc m) = cong (plusSucR n (SSuc m))

plusSucR ∷ ∀ a b. SNat a → SNat b → (a :+: 'Suc b) :~: 'Suc (a :+: b)
plusSucR SZero _ = Refl
plusSucR (SSuc a) b = cong (plusSucR a b)

-- data SNat (n ∷ Nat) where
--   SZero ∷ SNat 'Zero
--   SSuc ∷ SNat n → SNat ('Suc n)

--  2. plusAssoc ∷ ∀ a b c. SNat a → SNat b → SNat c → (a :+: b) :+: c :~: a :+: (b :+: c)
-- plusAssoc ∷ ∀ a b c. SNat a → SNat b → SNat c → (a :+: b) :+: c :~: a :+: (b :+: c)
-- plusAssoc SZero SZero SZero = Refl
-- plusAssoc SZero SZero (SSuc c) = Refl
-- plusAssoc SZero (SSuc b) SZero = Refl
-- plusAssoc SZero (SSuc b) (SSuc c) = Refl
-- plusAssoc (SSuc a) SZero SZero = cong (plusAssoc a SZero SZero)
-- plusAssoc (SSuc a) SZero (SSuc b) = cong (plusAssoc a SZero (SSuc b))
-- plusAssoc (SSuc a) (SSuc b) SZero = cong (plusAssoc a (SSuc b) SZero)
-- plusAssoc (SSuc a) (SSuc b) (SSuc c) = cong (plusAssoc a (SSrc b) (SSuc c))

plusAssoc ∷ ∀ a b c. SNat a → SNat b → SNat c → (a :+: b) :+: c :~: a :+: (b :+: c)
plusAssoc SZero _ _ = Refl
plusAssoc (SSuc a) b c = cong (plusAssoc a b c)

--  3. prodZeroL ∷ SNat a → 'Zero :*: a :~: 'Zero
-- prodZeroL ∷ SNat a → 'Zero :*: a :~: 'Zero
-- prodZeroL SZero = Refl
-- prodZeroL (SSuc a) = Refl

prodZeroL ∷ SNat a → 'Zero :*: a :~: 'Zero
prodZeroL _ = Refl

--  4. prodZeroR ∷ SNat a → (a :*: 'Zero) :~: 'Zero
prodZeroR ∷ SNat a → (a :*: 'Zero) :~: 'Zero
prodZeroR SZero = Refl
prodZeroR (SSuc a) = _ -- prodZeroR a

plusZeroR ∷ SNat n → (n :+: 'Zero) :~: n
plusZeroR SZero = Refl
plusZeroR (SSuc n) = _ -- congSuc (plusZeroR n)


--  5. plusCommut ∷ ∀ a b. SNat a → SNat b → (a :+: b) :~: (b :+: a)
-- plusCommut ∷ ∀ a b. SNat a → SNat b → (a :+: b) :~: (b :+: a)
-- plusCommut SZero SZero = Refl
-- plusCommut SZero (SSuc b) = cong (plusZeroRR b)
-- plusCommut (SSuc a) SZero = cong (sym (plusZeroRR a))
-- plusCommut (SSuc a) (SSuc b) = cong _ -- (plusCommut (SSuc a) b)

plusCommut ∷ ∀ a b. SNat a → SNat b → (a :+: b) :~: (b :+: a)
plusCommut SZero b = sym (plusZeroR b)
plusCommut (SSuc (pa ∷ SNat pa)) b = congSuc indh `trans` sym (plusSucR b pa)
  where
    indh ∷ (pa :+: b) :~: (b :+: pa)
    indh = plusCommut pa b

plusZeroRR ∷ SNat a → a :~: (a :+: 'Zero)
plusZeroRR SZero = Refl
plusZeroRR (SSuc a) = cong (plusZeroRR a)

-- _ ∷ (a :+: 'Suc b) :~: (b :+: 'Suc a)

plusCross ∷ SNat a → SNat b → (a :+: 'Suc b) :~: (b :+: 'Suc a)
plusCross SZero SZero = Refl
plusCross (SSuc a) SZero = cong (plusSucZero a)
plusCross SZero (SSuc b) = cong (sym (plusSucZero b))
plusCross a (SSuc b) = _ -- (plusCross (SSuc a) (SSuc b)) -- (plusCross (SSuc m) m)

-- plusCross2 ∷ SNat n → SNat m → (n :+: 'Suc ('Suc m)) :~: (m :+: 'Suc ('Suc n))
-- _ ∷ (a :+: 'Suc ('Suc b)) :~: (b :+: 'Suc ('Suc a))

plusSuc ∷ SNat a → SNat b → (a :+: 'Suc b) :~: ('Suc a :+: b)
plusSuc SZero SZero = Refl
plusSuc SZero (SSuc b) = Refl
plusSuc (SSuc a) SZero = cong (plusSucR a SZero)
plusSuc (SSuc a) b = cong (plusSucR a b)

--     _ ∷                          (n1 :+: 'Suc 'Zero) :~: 'Suc (n1 :+: 'Zero)
-- plusSucR ∷ ∀ a b. SNat a → SNat b → (a :+: 'Suc b)      :~: 'Suc (a :+: b)

plusSucZero ∷ SNat a → (a :+: 'Suc 'Zero) :~: 'Suc a
plusSucZero SZero = Refl
plusSucZero (SSuc a) = cong (plusSucZero a)

--  6. prodOneL ∷ SNat n → (One :*: n) :~: n
--  7. prodOneR ∷ SNat n → (n :*: One) :~: n
--  8. prodSucL ∷ ∀ a b. SNat a → SNat b → ('Suc a :*: b) :~: b :+: (a :*: b)
--  9. prodSucR ∷ ∀ a b. SNat a → SNat b → (a :*: 'Suc b) :~: a :+: (a :*: b)
-- 10. prodDistribR ∷ ∀ a b c. SNat a → SNat b → SNat c → (a :+: b) :*: c :~: (a :*: c) :+: (b :*: c)
-- 11. prodDistribL ∷ ∀ a b c. SNat a → SNat b → SNat c → a :*: (b :+: c) :~: (a :*: b) :+: (a :*: c)
-- 12. prodAssoc ∷ ∀ a b c. SNat a → SNat b → SNat c → (a :*: b) :*: c :~: a :*: (b :*: c)
-- 13. prodCommut ∷ ∀ a b. SNat a → SNat b → (a :*: b) :~: (b :*: a)
-- 14. powerZero ∷ a :^: 'Zero :~: One
-- 15. powerOne ∷ SNat a → a :^: One :~: a
-- 16. prodPower ∷ ∀ a b c. SNat a → SNat b → SNat c → (a :^: b) :*: (a :^: c) :~: a :^: (b :+: c)
-- 17. powerProd ∷ ∀ a b c. SNat a → SNat b → SNat c → (a :^: c) :*: (b :^: c) :~: (a :*: b) :^: c
-- 18. powerPower ∷ ∀ a b c. SNat a → SNat b → SNat c → (a :^: b) :^: c :~: a :^: (b :*: c)
