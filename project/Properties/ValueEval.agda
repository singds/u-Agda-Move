import Data.Nat
import project.Syntax as Syntax
import project.Typing as Typing

module project.Properties.ValueEval
    (Nm Ns Nf Nsf Nfa : Data.Nat.ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    where

open import project.Properties.Include Nm Ns Nf Nsf Nfa P

shift-val-eq :
      {d c : ℕ}
      {t : Term}
    → Value t
    → (shift d c t) ≡ t

shift-vec-val-eq :
      {d c : ℕ}
      {n : ℕ} {ts : Vec Term n}
    → ValueV ts
    → (shift-vec d c ts) ≡ ts

shift-val-eq {d} {c} Vnum = refl
shift-val-eq {d} {c} (Vstruct {ts = ts} vs)
    with shift-vec d c ts | shift-vec-val-eq {d} {c} vs
... | ts' | refl = refl
 
shift-vec-val-eq {d} {c} V[] = refl 
shift-vec-val-eq {d} {c} (_V∷_ {t = t} {ts = ts} v vs)
    with shift d c t | shift-vec d c ts | shift-val-eq {d} {c} v | shift-vec-val-eq {d} {c} vs
... | t' | ts' | refl | refl = refl




shift-back-val-eq :
      {c : ℕ}
      {t : Term}
    → Value t
    → (shift-back c t) ≡ t

shift-back-vec-val-eq :
      {c : ℕ}
      {n : ℕ} {ts : Vec Term n}
    → ValueV ts
    → (shift-back-vec c ts) ≡ ts

shift-back-val-eq {c} Vnum = refl
shift-back-val-eq {c} (Vstruct {ts = ts} vs)
    with shift-back-vec c ts | shift-back-vec-val-eq {c} vs
... | ts' | refl = refl
 
shift-back-vec-val-eq {c} V[] = refl 
shift-back-vec-val-eq {c} (_V∷_ {t = t} {ts = ts} v vs)
    with shift-back c t | shift-back-vec c ts | shift-back-val-eq {c} v | shift-back-vec-val-eq {c} vs
... | t' | ts' | refl | refl = refl




subst-val-eq :
      {i : ℕ}
      {t1 t2 : Term}
    → Value t2
    → subst i t1 t2 ≡ t2

subst-vec-val-eq :
      {i : ℕ}
      {t1 : Term}
      {n : ℕ} {ts : Vec Term n}
    → ValueV ts
    → subst-vec i t1 ts ≡ ts

subst-val-eq {i} Vnum = refl
subst-val-eq {i} {t1} (Vstruct {ts = ts} vs)
    with (subst-vec i t1 ts) | subst-vec-val-eq {i} {t1} vs
... | ts' | refl = refl
 
subst-vec-val-eq {i} V[] = refl 
subst-vec-val-eq {i} {t1} (_V∷_ {t = t} {ts = ts} v vs)
    with subst i t1 t | subst-vec i t1 ts | subst-val-eq {i} {t1} v | subst-vec-val-eq {i} {t1} vs
... | t' | ts' | refl | refl = refl




subst+back-val-eq :
      {i : ℕ}
      {t1 t2 : Term}
    → Value t2
    → subst+back i t1 t2 ≡ t2

subst+back-vec-val-eq :
      {i : ℕ}
      {t1 : Term}
      {n : ℕ} {ts : Vec Term n}
    → ValueV ts
    → subst+back-vec i t1 ts ≡ ts

subst+back-val-eq {i} {t1} {t2} v
    with subst i t1 t2 | subst-val-eq {i} {t1} v
... | t'  | refl with shift-back i t2 | shift-back-val-eq {i} {t2} v
... | t'' | refl = refl

subst+back-vec-val-eq {i} V[] = refl
subst+back-vec-val-eq {i} {t1} (_V∷_ {t = t} {ts = ts} v vs)
    with subst i t1 t | subst-vec i t1 ts | subst-val-eq {i} {t1} v | subst-vec-val-eq {i} {t1} vs
... | t'  | ts'  | refl | refl
    with shift-back i t | shift-back-vec i ts | shift-back-val-eq {i} v | shift-back-vec-val-eq {i} vs
... | t'' | ts'' | refl | refl = refl
