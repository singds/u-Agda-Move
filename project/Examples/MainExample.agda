module project.Examples.MainExample where

open import project.IncludeBase
open import Data.Vec using ([]; _∷_)


Nm = 1; Ns = 2; Nf = 8; Nsf = 2; Nfa = 2
open import project.Syntax Nm Ns Nf Nsf Nfa

CoinM    = #0
Owner    = sId CoinM #0; OwnerT = Tst Owner
Coin     = sId CoinM #1; CoinT  = Tst Coin

transfer      = fId CoinM #0
create        = fId CoinM #1
getOwner      = fId CoinM #2
deleteIf      = fId CoinM #3
createIf      = fId CoinM #4
dropError     = fId CoinM #5
doubleSpend   = fId CoinM #6
unbalancedUse = fId CoinM #7

□ : Type;   □ = Tint

CoinModule : Module
CoinModule = mod (
          str false (Tint ∷ □ ⨾)         -- Owner
        ∷ str true  (OwnerT ∷ Tint ⨾)    -- Coin
        ⨾
    ) (
        fun (CoinT{- C1 -} ∷ OwnerT{- O2 -} ⨾) Tint ( -- transfer
            unpack {- O1,V = -} v1{- C1 -} In
                Let {- C2 = -} pack Coin (v2{- O2 -} ∷ v0{- V -} ⨾) In
                    pub v0{- C2 -}
        )
        ∷ fun (OwnerT{- OW -} ∷ □ ⨾) Tint ( -- create
            pub (pack Coin (v1{- OW -} ∷ N0 ⨾))
        )
        ∷ fun (CoinT{- C -} ∷ □ ⨾) OwnerT ( -- getOwner
            Let {- O = -} 1{- C -} · #0 In
            Let pub v2{- C -} In
            v1{- O -}
        )
        ∷ fun (CoinT{- C -} ∷ Tint{- Y -} ⨾) Tint ( -- deleteIf
            if v0{- Y -} then
                unpack v1{- C -} In N0
            else
                pub v1{- C -}
        )
        ∷ fun (Tint{- Y -} ∷ OwnerT{- O -} ⨾) Tint ( -- createIf
            if v1{- Y -} then
                pub (pack Coin (v0{- O -} ∷ N0 ⨾))
            else
                N0
        )
        -- Errors
        ∷ fun (CoinT ∷ □ ⨾) Tint ( -- dropError
            N0
        )
        ∷ fun (CoinT{- C -} ∷ □ ⨾) Tint ( -- doubleSpend
            Let pub v1{- C -} In
            pub v2{- C -}
        )
        ∷ fun (CoinT{- C -} ∷ Tint{- Y -} ⨾) Tint ( -- unbalancedUse
            if v0{- Y -} then
                unpack v1{- C -} In N0
            else
                N0
        )
        ⨾
    )

P : Program
P = prog (CoinModule ⨾)

open import project.Typing Nm Ns Nf Nsf Nfa P

linCoinT   :   IsLinear CoinT;    linCoinT   = lin refl
¬linOwnerT : ¬ IsLinear OwnerT;   ¬linOwnerT (lin ())

wf1 : WellFun CoinM #0 -- transfer
wf1 = well (
    linCoinT I∷l ¬linOwnerT I∷
    I[ Tunpack (Tvar (Xs (XzL linCoinT)))
        (¬linOwnerT I∷ ¬linTint I∷ I[
            Tlet (Tpack (Tvar (Xs (Xs (Xz ¬linOwnerT))) T∷
                  Tvar (Xz ¬linTint) T∷ T[]))
            (linCoinT I∷l I[
                Tpub (Tvar (XzL linCoinT)) linCoinT
            ])
        ])
    ])

wf2 : WellFun CoinM #1 -- create
wf2 = well (
    ¬linOwnerT I∷ ¬linTint I∷ I[
        Tpub (Tpack (Tvar (Xs (Xz ¬linOwnerT)) T∷ Tnum T∷ T[])) linCoinT
    ]
    )

wf3 : WellFun CoinM #2 -- getOwner
wf3 = well (
    linCoinT I∷l ¬linTint I∷ I[
        Tlet (TselX (Xs (XzL linCoinT)) ¬linOwnerT)
        (¬linOwnerT I∷ I[
            Tlet (Tpub (Tvar (Xs (Xs (XzL linCoinT)))) linCoinT)
            (¬linTint I∷ I[
                Tvar (Xs (Xz ¬linOwnerT))
            ])
        ])
    ]
    )

wf4 : WellFun CoinM #3 -- deleteIf
wf4 = well (linCoinT I∷l ¬linTint I∷ I[
    Tif (Tvar (Xz ¬linTint))
        (Tunpack (Tvar (Xs (XzL linCoinT))) (¬linOwnerT I∷ ¬linTint I∷ I[ Tnum ]))
        (Tpub    (Tvar (Xs (XzL linCoinT))) linCoinT)
    ])

wf5 : WellFun CoinM #4 --createIf
wf5 = well (¬linTint I∷ ¬linOwnerT I∷ I[
    Tif (Tvar (Xs (Xz ¬linTint)))
        (Tpub (Tpack (Tvar (Xz ¬linOwnerT) T∷ Tnum T∷ T[])) linCoinT)
        (Tnum)
    ])

¬wf1 : ¬ WellFun CoinM #5 -- dropError
¬wf1 (well (nLin I∷ x))  = nLin linCoinT
¬wf1 (well (yLin I∷l (nLin I∷ I[ () ])))

¬wf2 : ¬ WellFun CoinM #6 -- doubleSpend
¬wf2 (well (nLin I∷ x))  = nLin linCoinT
¬wf2 (well (yLin I∷l (_ I∷ I[
        Tlet (Tpub (Tvar (Xs (Xz nLin))) _) ht2
    ]))) = nLin linCoinT
¬wf2 (well (_ I∷l (_ I∷ I[
        Tlet (Tpub (Tvar (Xs (XzL _))) _)
        (¬linTint I∷ I[
            Tpub (Tvar (Xs (Xs ()))) yLin
        ])
    ])))

¬wf3 : ¬ WellFun CoinM #7 -- unbalancedUse
¬wf3 (well (nLin I∷ x))  = nLin linCoinT
¬wf3 (well (yLin I∷l (nLin I∷ I[
        Tif (Tvar (Xz _)) ht2 ()
    ])))
 