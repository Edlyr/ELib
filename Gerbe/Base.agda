{-# OPTIONS --cubical #-}

module ELib.Gerbe.Base where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
--open import Cubical.Homotopy.Loopspace
--open import Cubical.Structures.Group
open import Cubical.Structures.Group hiding (⟨_⟩)
open import Cubical.Structures.AbGroup renaming (⟨_⟩ to Ab⟨_⟩)
open import ELib.Group.Morphism
open import Cubical.Data.Sigma
--open import ELib.B1.MorphismDelooping
--open import ELib.UsefulLemmas

private
  variable
    ℓ ℓ' ℓ'' : Level

isGerbe : Type ℓ → Type ℓ
isGerbe X = ∥ X ∥ × isGroupoid X × ((x y : X) → ∥ x ≡ y ∥) × ((x : X) → (p q : x ≡ x) → p ∙ q ≡ q ∙ p)

Gerbe : Type (ℓ-suc ℓ)
Gerbe {ℓ} = Σ (Type ℓ) isGerbe

⟨_⟩ : Gerbe → Type ℓ
⟨_⟩ = fst

gerbe-inhabited : (G : Gerbe {ℓ}) → ∥ ⟨ G ⟩ ∥
gerbe-inhabited G = fst (snd G)

gerbe-grpd : (G : Gerbe {ℓ}) → isGroupoid ⟨ G ⟩
gerbe-grpd G = fst (snd (snd G))

gerbe-conn : (G : Gerbe {ℓ}) → ((x y : ⟨ G ⟩) → ∥ x ≡ y ∥)
gerbe-conn G = fst (snd (snd (snd G)))

gerbe-comm : (G : Gerbe {ℓ}) → ((x : ⟨ G ⟩) → (p q : x ≡ x) → p ∙ q ≡ q ∙ p)
gerbe-comm G = snd (snd (snd (snd G)))

π : (G : Gerbe {ℓ}) (x : ⟨ G ⟩) → AbGroup {ℓ}
π G x = (x ≡ x) , _∙_ , ((gerbe-grpd G _ _ , assoc) , refl , (λ x → sym (rUnit x) , sym (lUnit x)) , λ x → sym x , rCancel x , lCancel x) , gerbe-comm G x

module S (G : Gerbe {ℓ}) where
  X = ⟨ G ⟩

  s-type : (x y : X) → Type ℓ
  s-type x y = Σ[ f ∈ ((x ≡ x) ≃ (y ≡ y)) ] ((p : x ≡ y) (q : x ≡ x) → f .fst q ≡ sym p ∙ q ∙ p)

  abstract
    s : (x y : X) → s-type x y
    s x y = fst (T x y) where
      T : (x y : X) → isContr (s-type x y)
      T x y = recPropTrunc isPropIsContr (λ x≡y → transport (λ i → isContr (s-type x (x≡y i))) base-case) (gerbe-conn G x y) where
        base-case : isContr (s-type x x)
        base-case = center , contr where
          center : s-type x x
          center = idEquiv _ , λ p q → sym (cong (λ r → (sym p) ∙ r) (gerbe-comm G x q p) ∙ compPathl-cancel _ _)

          contr : (f : s-type x x) → center ≡ f
          contr (f , !) = ΣProp≡ (λ f → isPropΠ2 λ p q → gerbe-grpd G _ _ _ _) id≡f where
            id≡f : fst center ≡ f
            id≡f = equivEq _ _ (funExt λ q → rUnit _ ∙ lUnit _ ∙ sym (! refl q))

  s-iso : (x y : X) → GroupIso (AbGroup→Group (π G x)) (AbGroup→Group (π G y))
  s-iso x y = s x y .fst , morph where
    H = AbGroup→Group (π G x)
    H' = AbGroup→Group (π G y)
    f = s x y .fst .fst
    ! : (r : x ≡ y) → _
    ! = s x y .snd
    _⋆_ = group-operation H
    _⨀_ = group-operation H'
    morph : isGroupHom H H' (fst (s x y .fst))
    morph = λ p q → recPropTrunc (group-is-set H' _ _) (λ r → 
      f (p ⋆ q)                            ≡⟨ ! r (p ∙ q) ⟩
      sym r ∙ (p ∙ q) ∙ r                  ≡⟨ (λ i → sym r ∙ (assoc p q r (~ i))) ⟩
      sym r ∙ p ∙ q ∙ r                    ≡⟨ cong (λ x → sym r ∙ p ∙ x ∙ r) (sym (compPathl-cancel r q)) ⟩
      sym r ∙ p ∙ (r ∙ sym r ∙ q) ∙ r      ≡⟨ cong (λ x → sym r ∙ p ∙ x) (sym (assoc _ _ _) ∙ cong (λ y → r ∙ y) (sym (assoc _ _ _))) ⟩
      sym r ∙ p ∙ r ∙ sym r ∙ q ∙ r        ≡⟨ assoc _ _ _ ∙ assoc _ _ _ ∙ cong (λ x → x ∙ sym r ∙ q ∙ r) (sym (assoc _ _ _)) ⟩
      (sym r ∙ p ∙ r) ∙ (sym r ∙ q ∙ r)    ≡⟨ sym (λ i → ! r p i ∙ ! r q i) ⟩
      f p ⨀ f q ∎) (gerbe-conn G x y)

linked-by-ab : (G : Gerbe {ℓ}) (A : AbGroup {ℓ'}) → Type (ℓ-max ℓ ℓ')
linked-by-ab {ℓ} {ℓ'} G Aab = Σ[ e ∈ ((x : ⟨ G ⟩) → GroupIso A (AbGroup→Group (π G x))) ]
  ((x y : ⟨ G ⟩) → compGroupIso A (H x) (H y) (e x) (s-iso x y) ≡ e y) where
  open S G
  A = AbGroup→Group Aab
  H : (x : _) → _
  H x = AbGroup→Group (π G x)

link-by-π : (G : Gerbe {ℓ}) (x : ⟨ G ⟩) → linked-by-ab G (π G x)
link-by-π G x = (λ y → s-iso x y) , λ y z →
  groupIsoEq (AbGroup→Group (π G x)) (AbGroup→Group (π G z)) _ _
  (equivEq _ _ (funExt λ t → recPropTrunc (gerbe-grpd G _ _ _ _) (λ py → recPropTrunc (gerbe-grpd G _ _ _ _) (λ pz →
    transport (λ i → s-fun (py i) (pz i) (s-fun x (py i) t) ≡ s-fun x (pz i) t)
      (! _)
  ) (gerbe-conn G x z)) (gerbe-conn G x y)))
  where
  open S G
  s-fun : (x : _) (y : _) → _
  s-fun x y = s x y .fst .fst
  ! : (t : _) → s-fun x x t ≡ t
  ! t = snd (s x x) refl t ∙ sym (rUnit _ ∙ lUnit _)

-------------------

module _ (G : Gerbe {ℓ}) (A : AbGroup {ℓ'}) (ℒ : linked-by-ab G A) where
  eA = fst ℒ
  condA = snd ℒ
  Agrp = AbGroup→Group A
  test : (B : AbGroup {ℓ'}) → linked-by-ab G B ≃ GroupIso (Agrp) (AbGroup→Group B)
  test B = isoToEquiv (iso f g sec retr) where
    Bgrp = AbGroup→Group B

    f : linked-by-ab G B → GroupIso Agrp Bgrp
    f (eB , condB) = isContrT .fst .fst where
      pre-f : (x : ⟨ G ⟩) → GroupIso Agrp Bgrp
      pre-f x = compGroupIso Agrp (AbGroup→Group (π G x)) Bgrp (eA x) (invGroupIso Bgrp (AbGroup→Group (π G x)) (eB x))
      
      T : Type _
      T = Σ[ i ∈ (GroupIso Agrp Bgrp) ] ((x : ⟨ G ⟩) (g : Ab⟨ A ⟩) → i .fst .fst g ≡ pre-f x .fst .fst g )

      isContrT : isContr T
      isContrT = recPropTrunc isPropIsContr (λ x₀ → (pre-f x₀ , λ x g → recPropTrunc (group-is-set Bgrp _ _)
        (λ p → cong (λ ok → pre-f ok .fst .fst g) p) (gerbe-conn G x₀ x)) ,
        λ f → ΣProp≡ (λ x → isPropΠ λ x₁ → isPropΠ λ g → group-is-set Bgrp _ _)
        (groupIsoEq Agrp Bgrp _ _ (equivEq _ _ (funExt λ g → sym (snd f _ g))))) (gerbe-inhabited G)

    assocGroupComp : ∀ {ℓ ℓ' ℓ'' ℓ''' : Level} → (F : Group {ℓ}) (G : Group {ℓ'}) (H : Group {ℓ''}) (I : Group {ℓ'''})
      (f : GroupIso F G) (g : GroupIso G H) (h : GroupIso H I) →
      compGroupIso F G I f (compGroupIso G H I g h) ≡ compGroupIso F H I (compGroupIso F G H f g) h
    assocGroupComp F G H I f g h = groupIsoEq F I _ _ (equivEq _ _ refl)

    g : GroupIso Agrp Bgrp → linked-by-ab G B
    g i = eB , coherence where
      j = invGroupIso Agrp Bgrp i
  
      eB : (x : ⟨ G ⟩) → GroupIso Bgrp (AbGroup→Group (π G x))
      eB x = compGroupIso Bgrp Agrp (AbGroup→Group (π G x)) j (eA x)

      coherence : _
      coherence x y =
        sym (assocGroupComp Bgrp Agrp (AbGroup→Group (π G x)) (AbGroup→Group (π G y)) j (eA x) (S.s-iso G x y)) ∙
        cong (λ ok → compGroupIso Bgrp Agrp (AbGroup→Group (π G y)) j ok) (condA x y)

    sec : section f g
    sec i = {!!}

    retr : retract f g
    retr (eB , condB) = ΣProp≡ (λ e → isPropΠ2 λ x y → {!!}) {!!}
  

{-postulate
  AbGroup-ua : (G G' : AbGroup {ℓ}) → GroupIso (AbGroup→Group G) (AbGroup→Group G') ≃ (G ≡ G')

Π : (G : Gerbe {ℓ}) → Σ[ A ∈ AbGroup {ℓ} ] (linked-by-ab G A)
Π {ℓ} G = fst contr where
  type = Σ[ A ∈ AbGroup {ℓ} ] (linked-by-ab G A)
  contr : isContr type
  contr = recPropTrunc isPropIsContr (λ x₀ → (π G x₀ , link-by-π G x₀) , λ A → {!!}
  --ΣPathP ((fst (AbGroup-ua (π G x₀) (A .fst)) (groupIsoInv (AbGroup→Group (A .fst)) (AbGroup→Group (π G x₀)) (A .snd .fst x₀))) , {!!})
    ) (fst (snd G)) where


  lemma : (A : AbGroup {ℓ}) → (linked-by-ab G A) → (B : AbGroup {ℓ}) → (linked-by-ab G B) ≃ (GroupIso (AbGroup→Group A) (AbGroup→Group B))
  lemma A link B = {!!}
-}

B² : (AbGroup {ℓ}) → Type (ℓ-suc ℓ)
B² {ℓ} A = Σ[ G ∈ Gerbe {ℓ} ] (linked-by-ab G A)

module tests (A : AbGroup {ℓ}) (G : B² A) where
  B2 = B² A
  carac : (G G' : B2) → (G ≡ G') ≃ (Σ (fst G ≡ fst G') (λ p → PathP (λ i → linked-by-ab (p i) A) (snd G) (snd G')))
  carac G G' = invEquiv Σ≃
