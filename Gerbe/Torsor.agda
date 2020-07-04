{-# OPTIONS --cubical #-}

module ELib.Gerbe.Torsor where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
open import Cubical.Structures.Group renaming (⟨_⟩ to Grp⟨_⟩)
open import Cubical.Structures.AbGroup renaming (⟨_⟩ to Ab⟨_⟩ ; AbGroup→Group to GRP)
open import Cubical.Data.Sigma

open import ELib.Torsor.Torsor
open import ELib.Gerbe.Base
open import ELib.Gerbe.Link
open import ELib.Gerbe.B2

private
  variable
    ℓ : Level

module _ (A : AbGroup {ℓ}) where
  PG : Gerbe {ℓ-suc ℓ}
  PG = gerbe (Torsor (GRP A)) (isgerbe ∣ PT _ ∣ isGroupoidTorsor conn comm) where
    pre-conn : (T : Torsor (GRP A)) → ∥ PT _ ≡ T ∥
    pre-conn T = recPropTrunc propTruncIsProp (λ t₀ → ∣ uaTorsor (trivialize T t₀) ∣) (Torsor.inhabited T)

    conn : (T T' : Torsor (GRP A)) → ∥ T ≡ T' ∥
    conn T T' = recPropTrunc propTruncIsProp (λ pT → recPropTrunc propTruncIsProp (λ pT' → ∣ sym pT ∙ pT' ∣) (pre-conn T')) (pre-conn T)

    pre-comm : (x y : PT _ ≡ PT _) → x ∙ y ≡ y ∙ x
    pre-comm x y = f-inj (x ∙ y) (y ∙ x) (isHom _ _ ∙ comm _ _ ∙ sym (isHom _ _)) where
      open AbGroup A
      equiv : GroupEquiv (ΩB (GRP A)) (GRP A)
      equiv = compGroupEquiv (groupequiv (idEquiv _) λ _ _ → refl) (finalLemma (GRP A))
      open GroupEquiv equiv
      f = fst eq
      f-inj : (a b : _) → f a ≡ f b → a ≡ b
      f-inj a b p = a ≡⟨ sym (secEq eq a) ⟩ invEq eq (f a) ≡⟨ cong (invEq eq) p ⟩ invEq eq (f b) ≡⟨ secEq eq b ⟩ b ∎

    comm : (x : _) → (p q : x ≡ x) → p ∙ q ≡ q ∙ p
    comm x = recPropTrunc (isPropΠ2 λ _ _ → isGroupoidTorsor _ _ _ _) (λ path →
      transport (cong (λ r → (p q : r ≡ r) → p ∙ q ≡ q ∙ p) path) pre-comm) (pre-conn x)

  principalLink : Link PG A
  principalLink = makeLink-pnt _ (groupequiv eq isHom)
    where open GroupEquiv (finalLemma (GRP A))
    -- here we can't use finalLemma directly, since even though (π PG PT) has
    -- the same Carrier and law as ΩB, they are not judgmentally equal.
