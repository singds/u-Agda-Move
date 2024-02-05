module project.Examples.SyntaxExamples where

open import project.IncludeBase
open import Data.Vec using ([]; _∷_)

open import project.Syntax 1 1 1 2 2

Coin = sId #0 #0
CoinT = Tst Coin
deleteCoin = fId #0 #0
owner = v1
amount = v0

m1 : Module
m1 = modDef (
        strDef false (Tint ∷ Tint ⨾) ⨾   -- Coin
    ) (
        funDef (CoinT ∷ Tint ⨾) Tint (   -- transferCoin
            unpack v0 In (
                Let pack Coin (v2 ∷ amount ⨾) In
                    N0
                    -- change with "publish v0"
                    -- publish v0
            )
        ) ⨾
    )

ms1 : Program
ms1 = prog (m1 ⨾)

t1 : Term
t1 = call deleteCoin ((pack Coin (N2 ⨾)) ⨾)

