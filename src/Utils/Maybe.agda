module Utils.Maybe where

open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.Nat using (suc)
open import Data.Fin using (Fin) renaming (suc to fsuc)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- just is injective

just-inj : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

-- inversion lemmas for Data.Maybe.map fsuc

map-just : ∀ {n} (v : Maybe (Fin n)) (j′ : Fin (suc n))
         → Data.Maybe.map fsuc v ≡ just j′ → ∃ λ j″ → v ≡ just j″ × j′ ≡ fsuc j″
map-just (just j″) j′ refl = j″ , refl , refl
map-just nothing j′ ()

map-nothing : ∀ {n} (v : Maybe (Fin n)) → Data.Maybe.map fsuc v ≡ nothing → v ≡ nothing
map-nothing nothing refl = refl
map-nothing (just _) ()
