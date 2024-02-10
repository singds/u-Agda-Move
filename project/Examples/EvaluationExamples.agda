module project.Examples.EvaluationExamples where

open import project.IncludeBase
open import Data.Vec using (_∷_)

Nm = 1
open import project.Syntax Nm 1 1 2 1

MyAsset      = sId #0 #0
MyAssetT     = Tst MyAsset
destroyAsset = fId #0 #0

p : Program
p = prog (
        mod (
            str true (Tint ∷ Tint ⨾) -- MyAsset
            ⨾
        ) (
            fun (MyAssetT ⨾) Tint ( -- destroyAsset
                unpack v0 In v0
            )
            ⨾
        ) ⨾
    )

open import project.Utility     Nm 1 1 2 1 p
open import project.Evaluation  Nm 1 1 2 1 p


pt3 : {M : Fin Nm} → M ∋ Let num 3 In var 0 ⇒ num 3
pt3 = Elet2 Vnum

pt4 : {M : Fin Nm} → M ∋ Let (num 0) In if (var 0) then (num 1) else (num 2) ⇒* num 2
pt4 = begin⇒
    Let (num 0) In if (var 0) then (num 1) else (num 2)   ⇒⟨ Elet2 Vnum ⟩
    if (num 0) then (num 1) else (num 2)                  ⇒⟨ Eiffalse ⟩
    num 2 ⇒∎



term1 : Term
term1 = Let (pack MyAsset (N1' ∷ N2' ⨾))
        In (call destroyAsset (v0' ⨾))

val-packed1 : Value (struct 0 MyAsset (N1' ∷ N2' ⨾))
val-packed1 = Vstruct (Vnum V∷ Vnum V∷ V[])


ev-term1 : #0 ∋ term1 ⇒* N2'
ev-term1 = begin⇒
    term1                                                                ⇒⟨ Elet (Epacked k0 (Vnum V∷ Vnum V∷ V[])) ⟩
    Let (struct k0 MyAsset (N1' ∷ N2' ⨾)) In (call destroyAsset (v0' ⨾))  ⇒⟨ Elet2 val-packed1 ⟩
    call destroyAsset ((struct k0 MyAsset (N1' ∷ N2' ⨾)) ⨾)               ⇒⟨ Ecalled (val-packed1 V∷ V[]) ⟩
    exec #0 (unpack (struct k0 MyAsset (N1' ∷ N2' ⨾)) In v0')            ⇒⟨ Eexec (Eunpacked ( Vnum V∷ Vnum V∷ V[] )) ⟩
    exec #0 (N2')                                                        ⇒⟨ Eexecuted Vnum ⟩
    N2' ⇒∎



term2 : Term
term2 = Let (pack MyAsset (N1' ∷ N2' ⨾))
        In (unpack v0' In v1')

ev-term2 : #0 ∋ term2 ⇒* N1'
ev-term2 = begin⇒
    term2                                                         ⇒⟨ Elet (Epacked k0 (Vnum V∷ Vnum V∷ V[])) ⟩
    Let (struct k0 MyAsset (N1' ∷ N2' ⨾)) In (unpack v0' In v1')  ⇒⟨ Elet2 val-packed1 ⟩
    unpack (struct k0 MyAsset (N1' ∷ N2' ⨾)) In v1'               ⇒⟨ Eunpacked (Vnum V∷ Vnum V∷ V[]) ⟩
    N1' ⇒∎



-- An example where a vector of terms must be evaluated:
--   that is, the terms in the vector are not values. 
term3 : Term
term3 = pack MyAsset ((Let (N1') In v0') ∷ (Let (N2') In v0') ⨾)


ev-term3 : #0 ∋ term3 ⇒* struct k0 MyAsset (N1' ∷ N2' ⨾)
ev-term3 = begin⇒
    term3                                      ⇒⟨ Epack ((Let (N1') In v0') E∷ (E[ Elet2 Vnum ] V[])) ⟩
    pack MyAsset ((Let (N1') In v0') ∷ N2' ⨾)  ⇒⟨ Epack (E[ Elet2 Vnum ] (Vnum V∷ V[])) ⟩
    pack MyAsset (N1' ∷ N2' ⨾)                 ⇒⟨ Epacked k0 (Vnum V∷ Vnum V∷ V[]) ⟩
    struct k0 MyAsset (N1' ∷ N2' ⨾) ⇒∎
