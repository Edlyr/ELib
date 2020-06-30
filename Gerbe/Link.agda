{-# OPTIONS --cubical #-}

module ELib.Gerbe.Link where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
open import Cubical.Data.Sigma
open import Cubical.Structures.Group hiding (⟨_⟩)
open import Cubical.Structures.AbGroup renaming (⟨_⟩ to Ab⟨_⟩ ; AbGroup→Group to GRP)

open import ELib.Gerbe.Base
open import ELib.Gerbe.S

open import ELib.B1.MorphismDelooping
open import ELib.UsefulLemmas

private
  variable
    ℓ ℓ' ℓ'' : Level

record IsLink (G : Gerbe {ℓ}) (A : AbGroup {ℓ'}) (e : (x : ⟨ G ⟩) → Ab⟨ π G x ⟩ → Ab⟨ A ⟩) : Type (ℓ-max ℓ ℓ') where
  constructor islink
  open S G
  field
    e-eq : (x : ⟨ G ⟩) → isEquiv (e x)
    e-hom : (x : ⟨ G ⟩) → isGroupHom (GRP (π G x)) (GRP A) (e x)

record Link (G : Gerbe {ℓ}) (A : AbGroup {ℓ'}) : Type (ℓ-max ℓ ℓ') where
  constructor link
  field
    e : (x : ⟨ G ⟩) → Ab⟨ π G x ⟩ → Ab⟨ A ⟩
    isLink : IsLink G A e

  open S G public
  open IsLink isLink public

  eq : (x : ⟨ G ⟩) → Ab⟨ π G x ⟩ ≃ Ab⟨ A ⟩
  eq x = (e x , e-eq x)

  hom : (x : ⟨ G ⟩) → AbGroupHom (π G x) A
  hom x = grouphom (e x) (e-hom x)

  group-equiv : (x : ⟨ G ⟩) → AbGroupEquiv (π G x) A
  group-equiv x = groupequiv (eq x) (e-hom x)

  coherence : (x y : ⟨ G ⟩) → e x ≡ e y ∘ s x y
  coherence x y = recPropTrunc (isSetΠ (λ _ → AbGroup.is-set A) _ _) (λ p → transport
    (cong (λ y → e x ≡ e y ∘ s x y) p) lemma) (Gerbe.conn G x y) where
    lemma : e x ≡ e x ∘ s x x
    lemma = λ i → e x ∘ s-id x (~ i)

  coherence-inv : (x y : ⟨ G ⟩) → invEq (eq x) ≡ s y x ∘ invEq (eq y)
  coherence-inv x y = recPropTrunc (isSetΠ (λ _ → AbGroup.is-set (π G x)) _ _) (λ p → transport
    (cong (λ y → invEq (eq x) ≡ s y x ∘ invEq (eq y)) p) lemma) (Gerbe.conn G x y) where
    lemma : invEq (eq x) ≡ s x x ∘ invEq (eq x)
    lemma = λ i → s-id x (~ i) ∘ invEq (eq x)

trivialLink : (G : Gerbe {ℓ}) (x : ⟨ G ⟩) → Link G (π G x)
trivialLink G x₀ = link (λ x → s x x₀) (islink (λ x → isEquiv-s x x₀) (λ x → isHom-s x x₀))
  where open S G

makeLink-pnt : (G : Gerbe {ℓ}) {A : AbGroup {ℓ'}} {x₀ : ⟨ G ⟩} → AbGroupEquiv (π G x₀) A → Link G A
makeLink-pnt G {A = A} {x₀ = x₀} f = link (λ x → GroupEquiv.eq (e x) .fst)
  (islink (λ x → GroupEquiv.eq (e x) .snd) (λ x → GroupEquiv.isHom (e x))) where
  e : (x : ⟨ G ⟩) → AbGroupEquiv (π G x) A
  e x = compGroupEquiv (S.s-groupEquiv G x x₀) f

congHom : ∀ (G : Gerbe {ℓ}) (H : Gerbe {ℓ'}) (f : ⟨ G ⟩ → ⟨ H ⟩) (x : ⟨ G ⟩) → AbGroupHom (π G x) (π H (f x))
congHom G H f x = grouphom (cong f) (cong-∙ f)

congLink-pnt : ∀ {ℓA ℓB} {G : Gerbe {ℓ}} {H : Gerbe {ℓ'}} {A : AbGroup {ℓA}} {B : AbGroup {ℓB}} →
  Link G A → Link H B → (⟨ G ⟩ → ⟨ H ⟩) → ⟨ G ⟩ → AbGroupHom A B
congLink-pnt {G = G} {H = H} {A = A} {B = B} lA lB f x₀ = grouphom fun (GroupHom.isHom test) where
  module lA = Link lA
  module lB = Link lB
  fun : Ab⟨ A ⟩ → Ab⟨ B ⟩
  fun = lB.e (f x₀) ∘ cong f ∘ invEq (lA.eq x₀)

  test : AbGroupHom A B
  test = compGroupHom (GroupEquiv.hom (invGroupEquiv (lA.group-equiv x₀))) (compGroupHom (congHom G H f x₀) (lB.hom (f x₀)))

module _ {ℓA ℓB} {G : Gerbe {ℓ}} {H : Gerbe {ℓ'}} {A : AbGroup {ℓA}} {B : AbGroup {ℓB}}
  (lA : Link G A) (lB : Link H B) (g : ⟨ G ⟩ → ⟨ H ⟩) where
  congLinkType : Type _
  congLinkType = Σ[ f ∈ (AbGroupHom A B) ] ((x : ⟨ G ⟩) → f ≡ congLink-pnt lA lB g x)

  isPropCongLinkType : isProp congLinkType
  isPropCongLinkType = recPropTrunc isPropIsProp
    (λ x f f' → Σ≡Prop (λ _ → isPropΠ λ _ → isSetGroupHom _ _) (snd f x ∙ sym (snd f' x)))
    (Gerbe.inhabited G)

  congLink-def : congLinkType
  congLink-def = recPropTrunc isPropCongLinkType (λ x₀ → congLink-pnt lA lB g x₀ , lemma x₀) (Gerbe.inhabited G) where
    lemma : (x y : ⟨ G ⟩) → congLink-pnt lA lB g x ≡ congLink-pnt lA lB g y
    lemma x y = recPropTrunc (isSetGroupHom _ _) (cong (λ x → congLink-pnt lA lB g x)) (Gerbe.conn G x y)

  abstract
    congLink : AbGroupHom A B
    congLink = fst congLink-def

    congLink-carac : (x : ⟨ G ⟩) → congLink ≡ congLink-pnt lA lB g x
    congLink-carac = snd congLink-def

congLink-comp : ∀ {ℓA ℓB ℓC} {G : Gerbe {ℓ}} {H : Gerbe {ℓ'}} {F : Gerbe {ℓ''}} {A : AbGroup {ℓA}} {B : AbGroup {ℓB}} {C : AbGroup {ℓC}}
  (lA : Link G A) (lB : Link H B) (lC : Link F C) (g : ⟨ G ⟩ → ⟨ H ⟩) (f : ⟨ H ⟩ → ⟨ F ⟩) →
  congLink lA lC (f ∘ g) ≡ compGroupHom (congLink lA lB g) (congLink lB lC f)
congLink-comp {G = G} {H = H} lA lB lC g f = recPropTrunc (isSetGroupHom _ _) lemma (Gerbe.inhabited G) where
  lemma : (x : ⟨ G ⟩) → congLink lA lC (f ∘ g) ≡ compGroupHom (congLink lA lB g) (congLink lB lC f)
  lemma x =
    congLink lA lC (f ∘ g)
      ≡⟨ congLink-carac lA lC (f ∘ g) x ⟩
    congLink-pnt lA lC (f ∘ g) x
      ≡⟨ groupHomEq subLemma ⟩
    compGroupHom (congLink-pnt lA lB g x) (congLink-pnt lB lC f (g x))
      ≡⟨ (λ i → compGroupHom (congLink-carac lA lB g x (~ i)) (congLink-carac lB lC f (g x) (~ i))) ⟩
    compGroupHom (congLink lA lB g) (congLink lB lC f) ∎ where
    module lA = Link lA
    module lB = Link lB
    module lC = Link lC
    subLemma : lC.e (f (g x)) ∘ (cong (f ∘ g)) ∘ invEq (lA.eq x) ≡
               lC.e (f (g x)) ∘ cong f ∘ invEq (lB.eq (g x)) ∘ lB.e (g x) ∘ cong g ∘ invEq (lA.eq x)
    subLemma = cong (λ r → lC.e (f (g x)) ∘ cong f ∘ r ∘ cong g ∘ invEq (lA.eq x))
      (sym (funExt (secEq (lB.eq (g x)))))

module _ {ℓA ℓB} {G : Gerbe {ℓ}} {H : Gerbe {ℓ'}} {A : AbGroup {ℓA}} {B : AbGroup {ℓB}}
  (lA : Link G A) (lB : Link H B) (f : AbGroupHom A B) (x₀ : ⟨ G ⟩) (y₀ : ⟨ H ⟩) where
  deloopType : Type _
  deloopType = Σ[ g ∈ (⟨ G ⟩ → ⟨ H ⟩) ] (y₀ ≡ g x₀) × (congLink lA lB g ≡ f)

  module lA = Link lA
  module lB = Link lB
  f' : x₀ ≡ x₀ → y₀ ≡ y₀
  f' = invEq (lB.eq y₀) ∘ GroupHom.fun f ∘ lA.e x₀

  f'test : AbGroupHom (π G x₀) (π H y₀)
  f'test = compGroupHom (lA.hom x₀) (compGroupHom f (GroupEquiv.hom (invGroupEquiv (lB.group-equiv y₀))))

  module Deloop = Delooping (Gerbe.conn G) (Gerbe.grpd H) f' (GroupHom.isHom f'test)

  caracDeloopType : deloopType ≃ Deloop.deloopingType
  caracDeloopType = isoToEquiv (iso eq→ eq← sec retr) where
    eq→ : deloopType → Deloop.deloopingType
    eq→ (g , p , coh) = g , p ,
      λ q → 
        p ∙ cong g q
          ≡⟨ cong (p ∙_) (λ i → testok i q) ⟩
        p ∙ lB.s y₀ (g x₀) (f' q)
          ≡⟨ cong (p ∙_) (lB.s-carac y₀ (g x₀) p (f' q)) ⟩
        p ∙ (sym p) ∙ f' q ∙ p
          ≡⟨ compPathl-cancel p _ ⟩
        f' q ∙ p ∎
      where
      testok : cong g ≡ S.s H y₀ (g x₀) ∘ f'
      testok =
        cong g
          ≡⟨ (λ i → funExt (secEq (lB.eq (g x₀))) (~ i) ∘ cong g ∘ funExt (secEq (lA.eq x₀)) (~ i)) ⟩
        invEq (lB.eq (g x₀)) ∘ lB.e (g x₀) ∘ cong g ∘ invEq (lA.eq x₀) ∘ lA.e x₀
          ≡⟨ cong (λ r → invEq (lB.eq (g x₀)) ∘ r ∘ lA.e x₀) (cong GroupHom.fun (sym (congLink-carac lA lB g x₀) ∙ coh)) ⟩
        invEq (lB.eq (g x₀)) ∘ GroupHom.fun f ∘ lA.e x₀
          ≡⟨ cong (λ r → r ∘ GroupHom.fun f ∘ lA.e x₀) (lB.coherence-inv (g x₀) y₀) ⟩
        S.s H y₀ (g x₀) ∘ f' ∎

    eq← : Deloop.deloopingType → deloopType
    eq← (g , p , !) = g , p , congLink-carac lA lB g x₀ ∙ groupHomEq (
      lB.e (g x₀) ∘ cong g ∘ invEq (lA.eq x₀)
        ≡⟨ cong (λ h → lB.e (g x₀) ∘ h ∘ cong g ∘ invEq (lA.eq x₀)) (sym (S.s-id H (g x₀)) ∙ S.s-comp H _ _ _) ⟩
      lB.e (g x₀) ∘ S.s H y₀ (g x₀) ∘ S.s H (g x₀) y₀ ∘ cong g ∘ invEq (lA.eq x₀)
        ≡⟨ cong (λ h → h ∘ S.s H (g x₀) y₀ ∘ cong g ∘ invEq (lA.eq x₀)) (sym (lB.coherence y₀ (g x₀))) ⟩
      lB.e y₀ ∘ S.s H (g x₀) y₀ ∘ cong g ∘ invEq (lA.eq x₀)
        ≡⟨ cong (λ h → lB.e y₀ ∘ h ∘ cong g ∘ invEq (lA.eq x₀)) (funExt (S.s-carac H _ _ (sym p))) ⟩
      lB.e y₀ ∘ (λ q → p ∙ cong g q ∙ sym p) ∘ invEq (lA.eq x₀)
        ≡⟨ cong (λ h → lB.e y₀ ∘ h ∘ invEq (lA.eq x₀)) (funExt λ q →
          p ∙ cong g q ∙ sym p
            ≡⟨ assoc _ _ _ ∙ cong (_∙ sym p) (! q) ⟩
          (f' q ∙ p) ∙ sym p
            ≡⟨ compPathr-cancel _ _ ⟩
          f' q ∎
        )⟩
      lB.e y₀ ∘ f' ∘ invEq (lA.eq x₀)
        ≡⟨ refl ⟩
      lB.e y₀ ∘ invEq (lB.eq y₀) ∘ GroupHom.fun f ∘ lA.e x₀ ∘ invEq (lA.eq x₀)
        ≡⟨ (λ i → funExt (retEq (lB.eq y₀)) i ∘ GroupHom.fun f ∘ funExt (retEq (lA.eq x₀)) i) ⟩
      GroupHom.fun f ∎)

    sec : section eq→ eq←
    sec (g , p , !) = Deloop.propDeloop _ _

    retr : retract eq→ eq←
    retr (g , coh) = ΣPathP (refl , Σ≡Prop (λ _ → isSetGroupHom _ _) refl)

  deloopUnique : isContr deloopType
  deloopUnique = isOfHLevelRespectEquiv 0 (invEquiv caracDeloopType) (Deloop.deloop , Deloop.propDeloop _)
