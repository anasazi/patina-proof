open import Common
open import Id.Var
open import Syntax.VarDecl
open import Syntax.Type
module Context.TypeMap where

TMap = List (List VarDecl)

-- vtype
_⊢_∶_ : TMap → Var → Type → Set
T ⊢ x ∶ τ = Any (Any (_≡_ x ∘ VarDecl.var)) T

open import Syntax.Mut
open import Id.Life
open import Id.Struct
test-T : TMap
test-T = [ ([ test-i ∶ int
           ,, test-p ∶ (~ int)
           ])
        ,, ([ test-a ∶ struct test-A []
           ,, test-b ∶ struct test-B ([ `static ])
           ,, test-c ∶ struct test-C ([ `static ])
           ,, test-q ∶ & test-b1 imm int
           ,, test-r ∶ ~ int
           ,, test-s ∶ opt (~ int)
           ])
         ]

test-vtype-1 : test-T ⊢ test-i ∶ int
test-vtype-1 = Z (Z refl)
test-vtype-2 : test-T ⊢ test-c ∶ struct test-C ([ `static ])
test-vtype-2 = S (Z (S (S (Z refl))))
