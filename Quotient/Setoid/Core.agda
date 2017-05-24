module Quotient.Setoid.Core where

open import Quotient.Basic

open import Relation.Binary public
  using (IsEquivalence)

record Setoid c p : Set (lsuc (c ⊔ p)) where
  infix 4 _[_≈_]
  field
    Of : Set c
    _[_≈_] : Of → Of → Set p

    isEquivalence : IsEquivalence _[_≈_]

  open IsEquivalence isEquivalence public

open Setoid public
