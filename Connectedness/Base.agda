{-# OPTIONS --cubical --safe #-}
module ELib.Connectedness.Base where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Data.Sigma
open import Cubical.Data.Prod

private
  variable
    ℓ : Level
    A : Type ℓ

isConnected : Type ℓ → Type ℓ
isConnected A = (x y : A) → ∥ x ≡ y ∥

isPointConnected : Type ℓ → Type ℓ
isPointConnected A = Σ[ a ∈ A ] ((x : A) → ∥ a ≡ x ∥)

connectedComponent : (A : Pointed ℓ) → Pointed ℓ
connectedComponent A = (Σ[ x ∈ fst A ] ∥ x ≡ snd A ∥) , (snd A , ∣ refl ∣)
