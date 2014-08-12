open import Common
open import Id.Struct
open import Id.Life
open import Syntax.Variance
open import Syntax.Type
module Syntax.StructDecl where

record StructDecl : Set where
  constructor struct
  field
    name : Struct
    params : List (Vari × Life)
    fields : List Type

open import Syntax.Mut
test-sd-A test-sd-B test-sd-C test-sd-D test-sd-E : StructDecl
test-sd-A = struct test-A [] ([ int ])
test-sd-B = struct test-B ([ con , test-l0 ]) ([ int
                                              ,, & test-l0 mut int
                                              ])
test-sd-C = struct test-C ([ con , test-l0 ]) ([ struct test-A []
                                              ,, struct test-B ([ test-l0 ])
                                              ])
test-sd-D = struct test-D ([ con , test-l0 ]) ([ struct test-C ([ test-l0 ])
                                              ,, struct test-A []
                                              ,, struct test-C ([ test-l0 ])
                                              ,, struct test-B ([ test-l0 ])
                                              ])
test-sd-E = struct test-E [] ([ ~ int ])
