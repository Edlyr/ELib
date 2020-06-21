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
{-
isMorphism : (G : Group {ℓ}) (H : Group {ℓ'}) → (⟨ G ⟩ → ⟨ H ⟩) → Type (ℓ-max ℓ ℓ')
isMorphism G H f = (g g' : ⟨ G ⟩) → f (g ⋆¹ g') ≡ (f g ⋆² f g') where
  _⋆¹_ = group-operation G
  _⋆²_ = group-operation H

isPropIsMorphism : (G : Group {ℓ}) (H : Group {ℓ'}) (f : ⟨ G ⟩ → ⟨ H ⟩) → isProp (isMorphism G H f)
isPropIsMorphism G H f = isPropΠ2 λ _ _ → group-is-set H _ _

Hom : (G : Group {ℓ}) (H : Group {ℓ'}) → Type (ℓ-max ℓ ℓ')
Hom G H = Σ (⟨ G ⟩ → ⟨ H ⟩) (isMorphism G H)

isMorphismComp : (F : Group {ℓ}) (G : Group {ℓ'}) (H : Group {ℓ''}) (f : Hom F G) (g : Hom G H) → isMorphism F H (fst g ∘ fst f)
isMorphismComp F G H (f , morph-f) (g , morph-g) x y = cong g (morph-f _ _) ∙ morph-g _ _

morphComp : (F : Group {ℓ}) (G : Group {ℓ'}) (H : Group {ℓ''}) → Hom F G → Hom G H → Hom F H
morphComp F G H f g = fst g ∘ fst f , isMorphismComp F G H f g

-- Group Isomorphisms

--GroupIso : (G : Group {ℓ}) (H : Group {ℓ'}) → Type (ℓ-max ℓ ℓ')
--GroupIso G H = Σ[ f ∈ ⟨ G ⟩ ≃ ⟨ H ⟩ ] isMorphism G H (fst f)

isMorphismInv : (G : Group {ℓ}) (H : Group {ℓ'}) (f : GroupIso G H) → isMorphism H G (invEq (fst f))
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

groupIsoInv : (G : Group {ℓ}) (H : Group {ℓ'}) → GroupIso G H → GroupIso H G
groupIsoInv G H (f , morph) = invEquiv f , isMorphismInv G H (f , morph)

groupIsoComp : (F : Group {ℓ}) (G : Group {ℓ'}) (H : Group {ℓ''}) → GroupIso F G → GroupIso G H → GroupIso F H
groupIsoComp F G H (f , morph-f)  (g , morph-g) = compEquiv f g , isMorphismComp F G H (fst f , morph-f) (fst g , morph-g)

{-group-ua : (G H : Group {ℓ}) → GroupIso G H → G ≡ H
group-ua G H ((f , eq) , morph) = cong (equivFun assocΣ)
  (ΣProp≡ (λ _ → group-axioms-isProp _ _)
  (ΣPathP (ua (f , eq) , toPathP (funExt λ x → funExt λ y → {!!}))))-}
-}
-- Dual group and inversion antimorphism

DualGroup : Group {ℓ} → Group {ℓ}
DualGroup G = makeGroup 0g (λ x y → y + x) -_ is-set (λ x y z → sym (Group.assoc G z y x)) lid rid invl invr where
  open Group G
  
DualGroupIso : (G : Group {ℓ}) → GroupIso G (DualGroup G)
DualGroupIso G = groupiso (f , isEquiv-f)  isMorph-f where
  module G = Group G
  _⨀_ = G._+_
  inv = G.-_
  
  f : ⟨ G ⟩ → ⟨ G ⟩
  f x = inv x

  isEquiv-f : isEquiv f
  isEquiv-f = snd (isoToEquiv (iso f f G.invInvo G.invInvo))

  isMorph-f : isGroupHom G (DualGroup G) f
  isMorph-f g h =
    inv (g ⨀ h) ≡⟨ sym (G.invUniqueL ((
      (inv h ⨀ inv g) ⨀ (g ⨀ h)
        ≡⟨ sym (G.assoc _ _ _) ∙ cong (inv h ⨀_) (G.assoc _ _ _ ∙ cong (_⨀ h) (G.invl g) ∙ G.lid h) ⟩
      inv h ⨀ h
        ≡⟨ G.invl h ⟩
      G.0g ∎))
    ) ⟩ (inv h ⨀ inv g) ∎

-- Characterising a group by an isomorphism
groupStructFromIso : (G : Group {ℓ}) → (H : Σ[ X ∈ Type ℓ' ] (X → X → X)) → (f : ⟨ G ⟩ ≃ fst H) →
  ((g g' : ⟨ G ⟩) → equivFun f (Group._+_ G g g') ≡ snd H (equivFun f g) (equivFun f g')) → Group {ℓ'}
groupStructFromIso G (X , _⋆_) (f , eq) morph-f =
  makeGroup-left
    (f G.0g)
    _⋆_
    (λ x → f (inv (g x)))
    (isOfHLevelRespectEquiv 2 (f , eq) G.is-set)
    (λ x y z → isInj-g _ _ (morph-g _ _ ∙ cong (g x ⨀_) (morph-g _ _) ∙ G.assoc _ _ _ ∙ sym (morph-g _ _ ∙ cong (_⨀ g z) (morph-g _ _))))
    (λ x → isInj-g _ _ (morph-g _ _ ∙ cong (_⨀ g x) (retEq (g , eq') G.0g) ∙ (G.lid (g x))))
    λ x → isInj-g _ _ (morph-g _ _ ∙ cong (_⨀ g x) (retEq (g , eq') _) ∙ G.invl (g x) ∙ sym (retEq (g , eq') G.0g))
  where
  module G = Group G
  _⨀_ = G._+_
  inv = G.-_
  
  g = invEq (f , eq)
  eq' : isEquiv g
  eq' = snd (invEquiv (f , eq))

  isInj-g : (x y : X) → g x ≡ g y → x ≡ y
  isInj-g x y = invEq (_ , isEquiv→isEmbedding eq' x y)
  
  isInj-f : (x y : ⟨ G ⟩) → f x ≡ f y → x ≡ y
  isInj-f x y = invEq (_ , isEquiv→isEmbedding eq x y)

  morph-g : (x x' : X) → g (x ⋆ x') ≡ g x ⨀ g x'
  morph-g x x' = isInj-f _ _ (
    f (g (x ⋆ x'))
      ≡⟨ retEq (f , eq) (x ⋆ x') ⟩
    x ⋆ x'
      ≡⟨ sym (λ i → retEq (f , eq) x i ⋆ retEq (f , eq) x' i) ⟩
    f (g x) ⋆ f (g x')
      ≡⟨ sym (morph-f (g x) (g x')) ⟩
    f (g x ⨀ g x') ∎)
