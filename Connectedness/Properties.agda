{-# OPTIONS --cubical --safe #-}
module ELib.Connectedness.Properties where

open import ELib.Connectedness.Base public
open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (elim to elimPropTrunc)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat

private
  variable
    ℓ : Level
    A : Type ℓ
    a : A

symTrunc : {a b : A} (p : ∥ a ≡ b ∥) → ∥ b ≡ a ∥
symTrunc p = elimPropTrunc (λ _ → propTruncIsProp) (λ p' → ∣ sym p' ∣) p

truncCompPath : {a b c : A} (p : ∥ a ≡ b ∥) (q : ∥ b ≡ c ∥) → ∥ a ≡ c ∥
truncCompPath p q = elimPropTrunc (λ _ → propTruncIsProp) (λ p' → elimPropTrunc (λ _ → propTruncIsProp) (λ q' → ∣ p' ∙ q' ∣) q) p

--------------------------

isPropIsConnected : isProp (isConnected A)
isPropIsConnected = isPropΠ λ _ → isPropΠ λ _ → propTruncIsProp

isPropIsPointConnected : (a : A) → isProp ((x : A) → ∥ a ≡ x ∥)
isPropIsPointConnected a = isPropΠ λ _ → propTruncIsProp

pointed×connected→pointConnected : (A × isConnected A) → isPointConnected A
pointed×connected→pointConnected = λ (a , f) → a , λ x → f a x

pointConnected→pointed×connected : isPointConnected A → (A × isConnected A)
pointConnected→pointed×connected = λ (a , f) → a , λ x y → truncCompPath (symTrunc (f x)) (f y)

pointConnected≃pointed×connected : isPointConnected A ≃ (A × isConnected A)
pointConnected≃pointed×connected = isoToEquiv (iso pointConnected→pointed×connected pointed×connected→pointConnected sec retr) where
  sec : _
  sec x = ΣPathP (refl , isPropIsConnected _ _)
  retr : _
  retr x = ΣPathP (refl , isPropIsPointConnected _ _ _)

-------------------------

connectedComponentPath : ∀ {ℓ : Level} (A : Pointed ℓ) (x y : fst (connectedComponent A)) → (fst x ≡ fst y) ≡ (x ≡ y)
connectedComponentPath (A , a) x y = isoToPath (iso
  (λ p → Σ≡Prop (λ _ → propTruncIsProp) p)
  (λ p → cong fst p)
  (λ p → cong ΣPathP (Σ≡Prop (λ q → isOfHLevelPathP 1 propTruncIsProp _ _) refl))
  (λ p → refl))

isConnectedConnectedComponent : (A : Pointed ℓ) → isPointConnected (fst (connectedComponent A))
isConnectedConnectedComponent (A , a) = (a , ∣ refl ∣) ,
  λ x → elimPropTrunc {A = fst x ≡ a} {P = λ _ → ∥ (a , ∣ refl ∣) ≡ x ∥}
    (λ _ → propTruncIsProp) (λ p → ∣ ΣPathP (sym p , toPathP (propTruncIsProp _ _)) ∣) (snd x)

isOfHLevelConnectedComponent : ∀ (A : Pointed ℓ) (n : ℕ) → isOfHLevel {ℓ} n (fst A) → isOfHLevel n (fst (connectedComponent A))
isOfHLevelConnectedComponent (A , a) 0 p = (a , ∣ refl ∣) , λ x → ΣPathP (sym (snd p a) ∙ snd p (fst x) , toPathP (propTruncIsProp _ _))
isOfHLevelConnectedComponent (A , a) 1 p x y = transport (connectedComponentPath _ _ _) (p (fst x) (fst y))
isOfHLevelConnectedComponent (A , a) (suc (suc n)) p x y = transport (λ i → isOfHLevel (suc n) (connectedComponentPath (A , a) x y i)) (p _ _)
