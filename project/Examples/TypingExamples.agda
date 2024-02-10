{-
#!/bin/bash

file="$1"
echo "replace in $file"

sed -i 's/Typing\.HasType\.//g' "$file"
sed -i 's/Typing\.IsLinear\.//g' "$file"
sed -i 's/Typing\.HasTypeV\.//g' "$file"
sed -i 's/Typing\.HasTypeI\.//g' "$file"

echo "replace done"
-}

module project.Examples.TypingExamples where

open import project.IncludeBase
open import Data.Vec using ([]; _∷_)


Nm = 1

open import project.Syntax Nm 2 1 1 1

M0 = #0
LinCoin     = sId #0 #1
LinCoinT    = Tst LinCoin
Coin        = sId #0 #0
CoinT       = Tst Coin
destroyCoin = fId #0 #0


p : Program
p = prog (
        modDef (
            strDef false (Tint ⨾) -- Coin
            ∷
            strDef true (Tint ⨾)  -- LinCoin
            ⨾
        ) (
            funDef (CoinT ⨾) Tint ( -- destroyCoin
                unpack v0 In v0
            )
            ⨾
        ) ⨾
    )


open import project.Utility Nm 2 1 1 1 p
open import project.Typing  Nm 2 1 1 1 p


-- Two usage-environments Γ1, Γ2 depending on the same environment Δ
Δ : Env 2;    Δ  = Tint    ∷ CoinT    ∷ []
Γ1 : UEnv Δ;  Γ1 = Tint • u∷ CoinT • u∷ []
Γ2 : UEnv Δ;  Γ2 = Tint ∘ u∷ CoinT • u∷ []

-- Type a variable
pt1 : {M : Fin Nm} → HasType M (Tint ∘ u∷ []) (var 0) Tint (Tint ∘ u∷ [])
pt1 = Tvar (Xz (λ ()))

-- Can't type a variable
pt2 : {M : Fin Nm} {T : Type} {Γ2 : UEnv (T ∷ [])}
      → HasType M (T • u∷ []) (var 0) T Γ2 → ⊥
pt2 (Tvar ())

-- pt2 ht = ?          do a case split on ht
-- pt2 (Tvar htx) = ?  do a case split on htx
-- pt2 (Tvar ())

-- call destroyCoin (pack Coin [2])
t1 : Term
t1 = call destroyCoin ((pack Coin (N2' ∷ [])) ∷ [])

-- Prove that t1 is well typed in module 0
wellTy-t1 : HasType M0 [] t1 Tint []
wellTy-t1 = Tcall (Tpack (Tnum T∷ T[]) T∷ T[])

-- The Coin type is not linear
¬L-Coin : ¬ (IsLinear (Tst Coin))
¬L-Coin (lin ())

L-LinCoin : IsLinear (Tst LinCoin)
L-LinCoin = lin refl


--  let x = pack Coin [2] in x
t2 : Term
t2 = Let (pack Coin (N2' ∷ [])) In v0'

-- Prove that t2 is well typed in module 0
wellTy-t2 : HasType M0 [] t2 (Tst Coin) []
wellTy-t2 = Tlet (Tpack (Tnum T∷ T[])) (¬L-Coin I∷ I[ Tvar (Xz λ lc → ¬L-Coin lc) ])


-- WE CAN'T COPY A LINEAR VALUE
--     let x = pack LinCoin [2] in
--     let y = x in
--     let z = x in
--    0
t8 : Term
t8 = Let (pack LinCoin (N2' ∷ []))  -- let introduces x
        In (Let v0'                 -- let introduces y
            In (Let v1'             -- let introduces z
                In N0'              -- this is not relevant
            )
        )

-- ¬wellTy-t8 : ∀ (T : Type) → ¬ HasType M0 [] t8 T []
-- ¬wellTy-t8 T (Tlet (Tpack htv) hti) = {!   !}


-- {-
-- WE CAN'T UNPACK TWICE A LINEAR VALUE

--     let x = pack LinCoin [2] in
--     unpack LinCoin { y } = x in
--     unpack LinCoin { z } = x in
--     z
-- -}
-- term3 : Term
-- term3 = Let (pack LinCoin (N2 ∷ []))   -- let introduces x
--         In (unpack v0                   -- unpack uses x and introduces y
--             In (unpack v1               -- this second unpack tries to use x again and introduces z
--                 In v0                   -- this is not relevant
--             )
--         )

-- ¬wellTy-term3 : ∀ (T : Type) → ¬ HasType M0 `[] term3 T `[]
-- ¬wellTy-term3 T (Tlet ¬lin
--                     (Tpack (Tnum T∷ T[]))
--                     (Tunpack (Tvar p) (x I∷ I[ Tunpack (TvarS (Tvar p2)) h ] ))) = p2 (lin refl)
-- ¬wellTy-term3 T (Tlet ¬lin
--                     (Tpack (Tnum T∷ T[]))
--                     (Tunpack (Tvar p) h)) = p (lin refl)
-- ¬wellTy-term3 T (Tlet ¬lin
--                     (Tpack (Tnum T∷ T[]))
--                     (Tunpack (TvarL yesLin) h3)) = ¬lin yesLin
-- ¬wellTy-term3 T (TletL (lin l)
--                     (Tpack (Tnum T∷ T[]))
--                     (Tunpack (Tvar p) x)) = p (lin l)
-- ¬wellTy-term3 T (TletL (lin l)
--                     (Tpack (Tnum T∷ T[]))
--                     (Tunpack (TvarL p1) (p2 I∷ I[ Tunpack (TvarS ()) p4 ])))
-- ¬wellTy-term3 T (TletL (lin l)
--                     (Tpack (Tnum T∷ T[]))
--                     (Tunpack (TvarL p1) (() I∷l h)))
-- -- ¬wellTy-term3 T (TletL (lin l) (Tpack (Tnum T∷ T[])) (Tunpack (TvarL p1) (p2 I∷l I[ Tunpack (TvarS ()) p4 ])))

-- -- TODO : Check this case
-- -- ¬wellTy-term3 .(Tst (sId _ _)) (TletL (lin l) (Tpack (Tnum T∷ T[])) (Tunpack (TvarL p1) (lin x I∷l h))) = {! !}



-- {-
-- WE CAN'T DROP A LINEAR VALUE

--     let x = pack LinCoin [2] in
--     0
-- -}
-- term4 : Term
-- term4 = Let (pack LinCoin (N2 ∷ [])) In N0

-- ¬wellTy-term4 : {Γ : Env} → ∀ (T : Type) → ¬ HasType M0 `[] term4 T Γ
-- ¬wellTy-term4 T (Tlet ¬lin (Tpack x₁) h2) = ¬lin (lin refl)
-- ¬wellTy-term4 T (TletL yesLin (Tpack x) ())

-- term7 : Term
-- term7 = Let (pack LinCoin (N2 ∷ [])) In (N0 , N1)

-- ¬wellTy-term7 : ∀ (T : Type) → ¬ HasType M0 `[] term7 T Γ
-- ¬wellTy-term7 T (Tlet ¬lin (Tpack x₁) h2) = ¬lin (lin refl)
-- ¬wellTy-term7 .Tint (TletL yesLin (Tpack x) (Tseq x₁ () Tnum))
-- -- Alternative demonstration for the last line:
-- -- ¬wellTy-term7 .Tint (TletL yesLin (Tpack x) (Tseq x₁ Tnum ())))


-- {-
-- WE CAN DROP A NON-LINEAR VALUE

--     let x = pack Coin [2] in
--     0
-- -}
-- term5 : Term
-- term5 = Let (pack Coin (N2 ∷ [])) In N0

-- wellTy-term5 : HasType M0 `[] term5 Tint `[]
-- wellTy-term5 = Tlet (λ { (lin ()) }) (Tpack (Tnum T∷ T[])) Tnum


-- {-
-- WE CAN'T DROP A LINEAR VALUE USING IT IN A SEQUENCE

--     let x = pack LinCoin [2] in
--     x;
--     0
-- -}

-- term6 : Term
-- term6 = Let (pack LinCoin (N2 ∷ [])) In (v0 , N0)

-- ¬wellTy-term6 : ∀ (T : Type) → ¬ HasType M0 `[] term6 T Γ
-- ¬wellTy-term6 T (Tlet  p (Tpack (Tnum T∷ T[])) h2) = p (lin refl)
-- ¬wellTy-term6 T (TletL p (Tpack (Tnum T∷ T[])) (Tseq p2 (TvarL x) h3)) = p2 p

-- {-
-- WE CAN USE A VARIABLE OF LINEAR TYPE IN THE SEOCOND TERM OF A SEQUENCE

--     let x = pack LinCoin [2] in
--         0;
--         x
-- -}
-- term9 : Term
-- term9 = Let (pack LinCoin (N2 ∷ []))
--         In (N0 , v0)

-- wellTy-term9 : HasType M0 `[] term9 LinCoinT `[]
-- wellTy-term9 = TletL (lin {#0} {#1} refl) (Tpack (Tnum T∷ T[])) (Tseq ¬linTint Tnum (TvarL (lin refl)))
