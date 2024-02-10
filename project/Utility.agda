
open import Data.Nat as Nat using (ℕ; suc; _<_)
import project.Syntax as Syntax

module project.Utility
    (Nm Ns Nf Nsf Nfa : ℕ)
    (P : Syntax.Program Nm Ns Nf Nsf Nfa)
    where

open Syntax Nm Ns Nf Nsf Nfa

open import Data.Fin as Fin using (Fin; #_)
open import Data.Vec as V using (Vec; lookup)
open import Data.Bool as B using (Bool; true; false)
open import Data.Empty as Empty using (⊥; ⊥-elim)

gMod : (m : Fin Nm) → Module
gMod m = lookup (Program.mods P) m

-- Get the stducts defined in a module
gStrs : (m : Fin Nm) → Vec Str Ns
gStrs m = Module.strs (gMod m)

-- Get a struct
gStr : (m : Fin Nm) → (s : Fin Ns) → Str
gStr m s = lookup (gStrs m) s

-- Check if a struct is linear
gIsLin : (m : Fin Nm) → (s : Fin Ns) → Bool
gIsLin m s = Str.isLin (lookup (gStrs m) s)

-- Get the list of fields of a struct
gFieldsT : (m : Fin Nm) → (s : Fin Ns) → Vec Type Nsf
gFieldsT m s = Str.fieldsT (gStr m s)



-- Get the functions defined in a module
gFuns : (m : Fin Nm) → Vec Fun Nf
gFuns m = Module.funs (gMod m)

-- Get a function
gFun : (m : Fin Nm) → (f : Fin Nf) → Fun
gFun m f = lookup (gFuns m) f

gArgsT : (m : Fin Nm) → (f : Fin Nf) → Vec Type Nfa
gArgsT m f = Fun.argsT (gFun m f)

gRetT : (m : Fin Nm) → (f : Fin Nf) → Type
gRetT m f = Fun.retT (gFun m f)

gBody : (m : Fin Nm) → (f : Fin Nf) → LTerm
gBody m f = Fun.body (gFun m f)

absurd = ⊥-elim
