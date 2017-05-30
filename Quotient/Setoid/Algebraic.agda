module Quotient.Setoid.Algebraic where

open import Quotient.Basic
open import Quotient.Setoid
open import Quotient.Function

data Or {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  left : A → Or A B
  right : B → Or A B

record Lift {a b} (A : Set a) : Set (a ⊔ b) where
  constructor lift
  field
    lower : A

data Or≈ {c d p q} (S : Setoid c p) (T : Setoid d q) : Rel (Or (Of S) (Of T)) (c ⊔ d ⊔ p ⊔ q) where
  left : ∀ {x y} → S [ x ≈ y ] → Or≈ S T (left x) (left y)
  right : ∀ {x y} → T [ x ≈ y ] → Or≈ S T (right x) (right y)

infixr 4 _⊎_

_⊎_ : ∀ {c d p q} → Setoid c p → Setoid d q → Setoid _ _
Of (S ⊎ T) = Or (Of S) (Of T)
_[_≈_] (S ⊎ T) = Or≈ S T
IsEquivalence.refl (isEquivalence (S ⊎ T)) {left x} = left (refl S)
IsEquivalence.refl (isEquivalence (S ⊎ T)) {right x} = right (refl T)
IsEquivalence.sym (isEquivalence (S ⊎ T)) (left eq) = left (sym S eq)
IsEquivalence.sym (isEquivalence (S ⊎ T)) (right eq) = right (sym T eq)
IsEquivalence.trans (isEquivalence (S ⊎ T)) (left e1) (left e2) = left (trans S e1 e2)
IsEquivalence.trans (isEquivalence (S ⊎ T)) (right e1) (right e2) = right (trans T e1 e2)

infixr 5 _×_
infixr 2 _,_

record And {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B

open And public

_×_ : ∀ {c d p q} → Setoid c p → Setoid d q → Setoid _ _
Of (S × T) = And (Of S) (Of T)
_[_≈_] (S × T) = λ x y → And (S [ fst x ≈ fst y ]) (T [ snd x ≈ snd y ])
IsEquivalence.refl (isEquivalence (S × T)) = refl S , refl T
IsEquivalence.sym (isEquivalence (S × T)) eq = sym S (fst eq) , sym T (snd eq)
IsEquivalence.trans (isEquivalence (S × T)) e1 e2 = trans S (fst e1) (fst e2) , trans T (snd e1) (snd e2)

curry : ∀ {c d e p q r} {S : Setoid c p} {T : Setoid d q} {U : Setoid e r} → Of (S × T ⇨ U) → Of (S ⇨ T ⇨ U)
curry {S = S} f = record
  { _∙_ = λ x → record
    { _∙_ = λ y → f ∙ (x , y)
    ; cong = λ eq → cong f (refl S , eq)
    }
  ; cong = λ e1 e2 → cong f (e1 , e2)
  }

uncurry : ∀ {c d e p q r} {S : Setoid c p} {T : Setoid d q} {U : Setoid e r} → Of (S ⇨ T ⇨ U) → Of (S × T ⇨ U)
uncurry {S = S} f = record
  { _∙_ = λ { (x , y) → f ∙ x ∙ y}
  ; cong = λ { (e1 , e2) → cong f e1 e2 }
  }
