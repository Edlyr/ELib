{-# OPTIONS --cubical #-}

module ELib.B2.Base where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
open import Cubical.HITs.SetTruncation renaming (rec to recSetTrunc ; elim to elimSetTrunc)
open import Cubical.Data.Sigma
--open import Cubical.Functions.FunExtEquiv
--open import Cubical.Functions.Embedding
open import ELib.Connectedness.Base
open import ELib.Connectedness.Properties
open import ELib.ConcreteGroup.Base
--open import Cubical.Homotopy.Loopspace
open import ELib.UniversalCover.Base
open import ELib.UsefulLemmas

ConcreteAbelianGroup : ∀ ℓ → Type (ℓ-suc ℓ)
ConcreteAbelianGroup ℓ = Σ[ A ∈ Pointed ℓ ] isConnected(fst A) × isConnected(snd A ≡ snd A) × is2Groupoid (fst A)

B² : ∀ {ℓ} → AbConcreteGroup ℓ → ConcreteAbelianGroup ((ℓ-suc ℓ))
B² {ℓ} (G , abG) =
  B ,
  isConnectedUniversalCover A ,
  isSimplyConnectedUniversalCover A ,
  2groupoid
  where
  open ConcreteGroup G
  A : Pointed (ℓ-suc ℓ)
  A = (Pointed ℓ) , Ptd
  B : Pointed (ℓ-suc (ℓ))
  B = UniversalCover A
  connUC = isConnectedUniversalCover A
  2groupoid : is2Groupoid (fst B)
  2groupoid x y =
    recPropTrunc isPropIsGroupoid  (λ px →
    recPropTrunc isPropIsGroupoid (λ py →
      transport (λ i → isGroupoid (px i ≡ py i))
        (transport (cong isGroupoid (ua Σ≡))
          (isGroupoidΣ (transport (cong isGroupoid (ua Σ≡))
            (isGroupoidΣ (isOfHLevel≡ 3 isGrpd isGrpd)
            λ _ → isSet→isGroupoid (transport (cong isSet (sym (PathP≡Path _ _ _))) (isGrpd _ _))))
          λ p → transport (cong isGroupoid (sym (PathP≡Path _ _ _))) (isSet→isGroupoid (isProp→isSet (setTruncIsSet _ _))))
        )
    ) (connUC (snd B) y))
    (connUC (snd B) x)

 
