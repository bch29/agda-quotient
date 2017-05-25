module Quotient.ISetoid.Core where

open import Quotient.Basic

open import Relation.Binary.Indexed public
  using ()
  renaming (IsEquivalence to IsEquivalence↑)

IRel : ∀ {a ℓ} {I : Set ℓ} → (I → Set a) → (p : _) → Set (a ⊔ ℓ ⊔ lsuc p)
IRel A p = ∀ {i j} → A i → A j → Set p

record ISetoid {ℓ} (I : Set ℓ) c p : Set (ℓ ⊔ lsuc (c ⊔ p)) where
  infix 4 _↑[_≈_]
  field
    Of↑ : I → Set c
    _↑[_≈_] : IRel Of↑ p

    isEquivalence↑ : IsEquivalence↑ Of↑ _↑[_≈_]

  open IsEquivalence↑ isEquivalence↑ public
    renaming
      ( refl to refl↑
      ; sym to sym↑
      ; trans to trans↑
      ; reflexive to reflexive↑
      )

open ISetoid public
