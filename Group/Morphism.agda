{-# OPTIONS --cubical #-}

module ELib.Group.Morphism where

open import Cubical.Foundations.Everything
open import Cubical.Functions.Embedding
open import Cubical.Structures.Group
open import Cubical.Data.Sigma

private
  variable
    ℓ ℓ' ℓ'' : Level

-- Group Homomorphisms

isMorphism : (G : Group {ℓ}) (H : Group {ℓ'}) → (⟨ G ⟩ → ⟨ H ⟩) → Type (ℓ-max ℓ ℓ')
isMorphism G H f = (g g' : ⟨ G ⟩) → f (g ⋆¹ g') ≡ (f g ⋆² f g') where
  _⋆¹_ = group-operation G
  _⋆²_ = group-operation H

isPropIsMorphism : (G H : Group {ℓ}) (f : ⟨ G ⟩ → ⟨ H ⟩) → isProp (isMorphism G H f)
isPropIsMorphism G H f = isPropΠ2 λ _ _ → group-is-set H _ _

Hom : (G : Group {ℓ}) (H : Group {ℓ'}) → Type (ℓ-max ℓ ℓ')
Hom G H = Σ (⟨ G ⟩ → ⟨ H ⟩) (isMorphism G H)

isMorphismComp : (F : Group {ℓ}) (G : Group {ℓ'}) (H : Group {ℓ''}) (f : Hom F G) (g : Hom G H) → isMorphism F H (fst g ∘ fst f)
isMorphismComp F G H (f , morph-f) (g , morph-g) x y = cong g (morph-f _ _) ∙ morph-g _ _

morphComp : (F : Group {ℓ}) (G : Group {ℓ'}) (H : Group {ℓ''}) → Hom F G → Hom G H → Hom F H
morphComp F G H f g = fst g ∘ fst f , isMorphismComp F G H f g

-- Group Isomorphisms

GroupIso : (G : Group {ℓ}) (H : Group {ℓ'}) → Type (ℓ-max ℓ ℓ')
GroupIso G H = Σ[ f ∈ ⟨ G ⟩ ≃ ⟨ H ⟩ ] isMorphism G H (fst f)

isMorphismInv : (G : Group {ℓ}) (H : Group {ℓ'}) (f : GroupIso G H) → isMorphism H G (equivFun (invEquiv (fst f)))
isMorphismInv G H  ((f , eq) , morph) h h' = isInj-f _ _ (
  f (g (h ⋆² h') )
    ≡⟨ retEq (f , eq) _ ⟩
  h ⋆² h'
    ≡⟨ sym (λ i → retEq (f , eq) h i ⋆² retEq (f , eq) h' i) ⟩
  f (g h) ⋆² f (g h')
    ≡⟨ sym (morph _ _) ⟩
  f (g h ⋆¹ g h') ∎)
  where
  _⋆¹_ = group-operation G
  _⋆²_ = group-operation H
  g = invEq (f , eq)
  isEmbedding-f : isEmbedding f
  isEmbedding-f = isEquiv→isEmbedding eq
  isInj-f : (x y : ⟨ G ⟩) → f x ≡ f y → x ≡ y
  isInj-f x y = invEq (_ , isEquiv→isEmbedding eq x y)

groupIsoComp : (F : Group {ℓ}) (G : Group {ℓ'}) (H : Group {ℓ''}) → GroupIso F G → GroupIso G H → GroupIso F H
groupIsoComp F G H (f , morph-f)  (g , morph-g) = compEquiv f g , isMorphismComp F G H (fst f , morph-f) (fst g , morph-g)

{-group-ua : (G H : Group {ℓ}) → GroupIso G H → G ≡ H
group-ua G H ((f , eq) , morph) = cong (equivFun assocΣ)
  (ΣProp≡ (λ _ → group-axioms-isProp _ _)
  (ΣPathP (ua (f , eq) , toPathP (funExt λ x → funExt λ y → {!!}))))-}

-- Dual group and inversion antimorphism

DualGroup : Group {ℓ} → Group {ℓ}
DualGroup (X , _⨀_ , (setX , assoc) , id , neutral , inv) =
  X ,
  (λ x y → y ⨀ x) ,
  (setX , λ x y z → sym (assoc z y x)) ,
  id ,
  (λ x → sym (G.rUnit x)) ,
  λ x → G.inv x , G.rCancel x
  where module G = GroupLemmas (X , _⨀_ , (setX , assoc) , id , neutral , inv)
  
InvGroupIso : (G : Group {ℓ}) → GroupIso G (DualGroup G)
InvGroupIso G = (f , isEquiv-f) , isMorph-f where
  module Ggrp = GroupLemmas G
  _⨀_ = Ggrp.op
  inv = Ggrp.inv
  
  f : ⟨ G ⟩ → ⟨ G ⟩
  f x = inv x

  isEquiv-f : isEquiv f
  isEquiv-f = snd (isoToEquiv (iso f f Ggrp.invInvo Ggrp.invInvo))

  isMorph-f : isMorphism G (DualGroup G) f
  isMorph-f g h =
    inv (g ⨀ h) ≡⟨ sym (Ggrp.invUniqueL _ _ ((
      (inv h ⨀ inv g) ⨀ (g ⨀ h)
        ≡⟨ (Ggrp.assoc _ _ _ ∙ cong (λ x → _ ⨀ x) (sym (Ggrp.assoc _ _ _) ∙ (cong (λ x → x ⨀ h) (Ggrp.lCancel g )) ∙ sym (Ggrp.lUnit h))) ⟩
      inv h ⨀ h
        ≡⟨ Ggrp.lCancel h ⟩
      Ggrp.id ∎))
    ) ⟩ (inv h ⨀ inv g) ∎
