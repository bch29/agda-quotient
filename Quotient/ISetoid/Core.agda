module Quotient.ISetoid.Core where

open import Quotient.Basic

open import Relation.Binary.Indexed public
  using ()
  renaming (IsEquivalence to IsEquivalence↑)

record ISetoid {ℓ} (I : Set ℓ) c p : Set (ℓ ⊔ lsuc (c ⊔ p)) where
  infix 4 _↑[_≈_]
  field
    Of↑ : I → Set c
    _↑[_≈_] : ∀ {i j} → Of↑ i → Of↑ j → Set p

    isEquivalence↑ : IsEquivalence↑ Of↑ _↑[_≈_]

  open IsEquivalence↑ isEquivalence↑ public
    renaming
      ( refl to refl↑
      ; sym to sym↑
      ; trans to trans↑
      ; reflexive to reflexive↑
      )

open ISetoid public
