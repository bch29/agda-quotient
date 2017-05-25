module Quotient.Example where

open import Quotient.Prelude
open import Quotient.Setoid.Higher

import Data.Nat as Nat
open Nat using (ℕ)

+ : Of (Prop ℕ ⇨ Prop ℕ ⇨ Prop ℕ)
+ = lift→² Nat._+_

* : Of (Prop ℕ ⇨ Prop ℕ ⇨ Prop ℕ)
* = lift→² Nat._*_

suc : Of (Prop ℕ ⇨ Prop ℕ)
suc = lift→ Nat.suc

pred : Of (Prop ℕ ⇨ Prop ℕ)
pred = lift→ Nat.pred

test : (Prop ℕ ⇨ Prop ℕ) [ id ≈ pred ∘ suc ]
test = app (id {S = Higher (Prop ℕ) at _})


test2 = Of↑ (Higher (Prop ℕ))
