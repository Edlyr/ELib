{-# OPTIONS --cubical #-}

module ELib.Gerbe.Torsor where

open import Cubical.Foundations.Everything
open import Cubical.HITs.PropositionalTruncation renaming (rec to recPropTrunc ; elim to elimPropTrunc)
open import Cubical.Structures.Group renaming (⟨_⟩ to Grp⟨_⟩)
open import Cubical.Structures.AbGroup renaming (⟨_⟩ to Ab⟨_⟩ ; AbGroup→Group to GRP)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import ELib.Torsor.Torsor
open import ELib.Gerbe.Base
open import ELib.Gerbe.Link
open import ELib.Gerbe.B2

private
  variable
    ℓ ℓ' : Level

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
  principalLink = makeLink-pnt (groupequiv eq isHom)
    where open GroupEquiv (finalLemma (GRP A))
    -- here we can't use finalLemma directly, since even though (π PG PT) has
    -- the same Carrier and law as ΩB, they are not judgmentally equal.

  torsors : B² A
  torsors = b² PG principalLink
  
----------

GroupProduct : Group {ℓ} → Group {ℓ'} → Group
GroupProduct G H = makeGroup-left 0X _⨀_ inv (isSet× G.is-set H.is-set)
  (λ a b c → ΣPathP (G.assoc (fst a) (fst b) (fst c) , H.assoc (snd a) (snd b) (snd c)))
  (λ a → ΣPathP (G.lid _ , H.lid _)) λ a → ΣPathP (G.invl _ , H.invl _) where
  module G = Group G
  module H = Group H
  X = G.Carrier × H.Carrier
  0X : X
  0X = G.0g , H.0g
  _⨀_ : X → X → X
  (g , h) ⨀ (g' , h') = (g G.+ g') , (h H.+ h')
  inv : X → X
  inv (g , h) = (G.- g , H.- h)

AbGroupProduct : AbGroup {ℓ} → AbGroup {ℓ'} → AbGroup
AbGroupProduct A B = makeAbGroup 0g _+_ -_ is-set assoc+ rid invr
  λ x y → ΣPathP (AbGroup.comm A _ _ , AbGroup.comm B _ _) where
  open Group (GroupProduct (GRP A) (GRP B)) renaming (assoc to assoc+)

_Ab×_ = AbGroupProduct

Hom+ : (A : AbGroup {ℓ}) → AbGroupHom (A Ab× A) A
Hom+ A = grouphom f isHom where
  open AbGroup A renaming (assoc to assoc+)
  f : Ab⟨ A Ab× A ⟩ → Ab⟨ A ⟩
  f (a , b) = a + b
  isHom : (x y : Ab⟨ A Ab× A ⟩) → ((fst x + fst y) + (snd x + snd y)) ≡ ((fst x + snd x) + (fst y + snd y))
  isHom (a , b) (c , d) =
    (a + c) + (b + d) ≡⟨ sym (assoc+ _ _ _) ⟩
    a + c + b + d     ≡⟨ cong (a +_) (assoc+ _ _ _ ∙ cong (_+ d) (comm _ _)) ⟩
    a + (b + c) + d   ≡⟨ cong (a +_) (sym (assoc+ _ _ _)) ⟩
    a + b + c + d     ≡⟨ assoc+ _ _ _ ⟩
    (a + b) + (c + d) ∎

B²prod : {A : AbGroup {ℓ}} {B : AbGroup {ℓ'}} {ℓG ℓH : Level} → B² A {ℓG} → B² B {ℓH} → B² (A Ab× B)
B²prod {A = A} {B = B} G H = b² _ lnk where -- Making the argument explicit would prevent agda from
                                            -- terminating type-checking in any reasonable amount of time
  module G = B² G
  module H = B² H
  module A = AbGroup A
  module B = AbGroup B
  module X = Gerbe (GerbeProduct G.grb H.grb)
  e : (x : X.Carrier) → x ≡ x → Ab⟨ A Ab× B ⟩
  e (x , y) p = G.e x (cong fst p) , H.e y (cong snd p)

  f : (x : X.Carrier) → Ab⟨ A Ab× B ⟩ → x ≡ x
  f (x , y) (p , q) = ΣPathP (invEq (G.eq x) p , invEq (H.eq y) q)
  
  abstract
    sec : (x : X.Carrier) → section (e x) (f x)
    sec (x , y) (p , q) = ΣPathP (retEq (G.eq x) p , retEq (H.eq y) q)
    retr : (x : X.Carrier) → retract (e x) (f x)
    retr (x , y) p = cong ΣPathP (ΣPathP (secEq (G.eq x) (cong fst p) , secEq (H.eq y) (cong snd p)))

    e-hom : (x : X.Carrier) → (p q : x ≡ x) → e x (p ∙ q) ≡
      ((G.e (fst x) (cong fst p) A.+ G.e (fst x) (cong fst q)) , (H.e (snd x) (cong snd p) B.+ H.e (snd x) (cong snd q)))
    e-hom (x , y) p q = ΣPathP (
      cong (G.e x) (cong-∙ fst p q) ∙ G.e-hom x _ _ ,
      cong (H.e y) (cong-∙ snd p q) ∙ H.e-hom y _ _)

  eq : (x : X.Carrier) → _
  eq x = isoToEquiv (iso (e x) (f x) (sec x) (retr x))

  lnk : Link (GerbeProduct G.grb H.grb) (A Ab× B)
  lnk = link e (islink (λ x → snd (eq x)) e-hom)

trivialGroup : AbGroup
trivialGroup = makeAbGroup tt (λ _ _ → tt) (λ _ → tt)
  (isProp→isSet (λ {tt tt → refl })) (λ _ _ _ → refl)
  (λ {tt → refl}) (λ _ → refl) λ _ _ → refl

neutralHom : (G : Group {ℓ}) → GroupHom (GRP trivialGroup) G
neutralHom G = grouphom (λ _ → Group.0g G) λ _ _ → sym (Group.rid G _)

BtrivialGroup : B² trivialGroup
BtrivialGroup = b² unitGerbe unitLink where
  unitGerbe : Gerbe
  unitGerbe = gerbe Unit (isgerbe ∣ tt ∣ (isSet→isGroupoid (isProp→isSet (λ {tt tt → refl}))) (λ {tt tt → ∣ refl ∣})
    λ _ _ _ → isProp→isSet (λ {tt tt → refl}) _ _ _ _)

  unitLink : Link unitGerbe trivialGroup
  unitLink = makeLink-pnt (groupequiv (isoToEquiv (iso (λ _ → tt) (λ _ → refl) (λ {tt → refl}) λ p → isProp→isSet (λ {tt tt → refl}) _ _ _ _))
    λ _ _ → refl)

trivialB² : isContr (B² trivialGroup)
trivialB² = BtrivialGroup , λ y → sym (uaB² _ (b²equiv (λ _ → tt) (groupHomEq (funExt (λ {tt → refl})))))

{-module GerbeAddition (A : AbGroup {ℓ}) where
  K² = B² A {ℓ-suc ℓ}

  PA : K²
  PA = torsors A

  TA : B².Carrier PA
  TA = principalTorsor (GRP A)

  _⊹_ : K² → K² → K²
  G ⊹ G' = 2-deloop PA TA (B²prod G G') where
    open Deloop2 (A Ab× A) A (Hom+ A)

  test-neutral : K²
  test-neutral = {!!}-}
{-
  module neutral (G : K²) where
    module G = B² G
    module PA = B² PA
    module A = AbGroup A

    torsor-G : G.Carrier → G.Carrier → Torsor (GRP A)
    torsor-G x y = torsor X _⋆_ is-torsor where
      X : Type _
      X = x ≡ y
      _⋆_ : X → Ab⟨ A ⟩ → X
      p ⋆ g = p ∙ invEq (G.eq y) g
      postulate
        is-torsor : IsTorsor (GRP A) X _⋆_
      {-is-torsor = istorsor (G.grpd x y) (G.conn x y)
        (λ p g g' →
          (p ∙ invEq (G.eq y) g) ∙ invEq (G.eq y) g' ≡⟨ sym (assoc _ _ _) ⟩
          p ∙ invEq (G.eq y) g ∙ invEq (G.eq y) g' ≡⟨ cong (p ∙_) (sym (isGroupHomInv (G.group-equiv y) g g')) ⟩
          p ∙ invEq (G.eq y) (g A.+ g') ∎)
        {!!} {!!} {!!} {!!}-}

    test : G.Carrier → PA.Carrier → Type _
    test x t = Σ[ y ∈ G.Carrier ] TorsorEquiv t (torsor-G x y)

    centerTA : (x : G.Carrier) → test x TA
    centerTA x = x , t-eq where
      t-eq : TorsorEquiv TA (torsor-G x x)
      t-eq = t-equiv eq is-t-equiv where
        eq : A.Carrier ≃ (x ≡ x)
        eq = invEquiv (G.eq x)
        is-t-equiv : (g g' : Ab⟨ A ⟩) → invEq (G.eq x) (g A.+ g') ≡ invEq (G.eq x) g ∙ invEq (G.eq x) g'
        is-t-equiv g g' = isGroupHomInv (G.group-equiv x) g g'

    contrTA : (x : G.Carrier) → isContr (test x TA)
    contrTA x = centerTA x , contr where
      contr : (y : test x TA) → centerTA x ≡ y
      contr (y , y-eq) = ΣPathP (p , toPathP (torsorEquivEq _ _ (equivEq _ _ (fromPathP lemma)))) where
        f = TorsorEquiv.eq y-eq .fst
        p : x ≡ y
        p = f A.0g
        lemma : PathP (λ i → A.Carrier → x ≡ (p i)) (invEq (G.eq x)) f
        lemma = funExt λ g → transport (sym (PathP≡compPath _ _ _)) (
          invEq (G.eq x) g ∙ f A.0g                         ≡⟨ sym (compPathl-cancel (f A.0g) _) ⟩
          f A.0g ∙ sym (f A.0g) ∙ invEq (G.eq x) g ∙ f A.0g ≡⟨ cong (f A.0g ∙_) (sym (G.s-carac x y (f A.0g) _)) ⟩
          f A.0g ∙ (G.s x y ∘ invEq (G.eq x)) g             ≡⟨ cong (λ ϕ → f A.0g ∙ ϕ g) (sym (G.coherence-inv y x)) ⟩
          f A.0g ∙ invEq (G.eq y) g                         ≡⟨ sym (TorsorEquiv.hom y-eq A.0g g) ⟩
          f (A.0g A.+ g)                                    ≡⟨ cong (λ g → f g) (A.lid g) ⟩
          f g ∎)

    contrT : (x : G.Carrier) (t : PA.Carrier) → isContr (test x t)
    contrT x t = recPropTrunc isPropIsContr (λ p → subst (λ t → isContr (test x t)) p (contrTA x)) (PA.conn TA t)

    contrT-TA : (x : G.Carrier) → contrT x TA ≡ contrTA x
    contrT-TA x = isPropIsContr _ _

    mapT : (α : B²prod G PA .B².Carrier) → test (fst α) (snd α)
    mapT (x , t) = contrT x t .fst

    cong-test : {x : G.Carrier} → (p : (x , TA) ≡ (x , TA)) → PathP (λ i → test (fst (p i)) (snd (p i))) (mapT (x , TA)) (mapT (x , TA))
    cong-test {x = x} p i = mapT (p i)

    neutralMap : B²prod G PA .B².Carrier → G.Carrier
    neutralMap (x , t) = contrT x t .fst .fst

    {-coherence : congLink (B².lnk (B²prod G PA)) G.lnk neutralMap ≡ Hom+ A
    coherence = groupHomEq {!!} where
      prod : B² (A Ab× A)
      prod = B²prod G PA
      module prod = B² prod

      lemma : (x : G.Carrier) → congLink-pnt (B².lnk (B²prod G PA)) G.lnk neutralMap (x , TA) ≡ Hom+ A
      lemma x = groupHomEq (funExt {!subLemma!}) where
        x₀ = (x , TA)
        r₀ : neutralMap x₀ ≡ x
        r₀ = cong (fst ∘ fst) (contrT-TA x)
        carac-cong : (p : x ≡ x) (q : TA ≡ TA) → cong {x = x₀} {y = x₀} neutralMap (ΣPathP (p , q)) ≡
          r₀ ∙ {!!} ∙ sym r₀
        carac-cong = {!!}
        {-subLemma : (α : Ab⟨ A Ab× A ⟩) → (G.e (neutralMap x₀) ∘ cong neutralMap ∘ invEq (prod.eq x₀)) α ≡ (fst α A.+ snd α)
        subLemma (g , g') =
          G.e (neutralMap x₀) (cong neutralMap (invEq (prod.eq x₀) (g , g'))) ≡⟨ refl ⟩
          G.e (neutralMap x₀) (cong neutralMap (ΣPathP (invEq (G.eq x) g , invEq (PA.eq TA) g'))) ≡⟨ {!!} ⟩
          g A.+ g' ∎-}
-}

  module tests where
    open neutral PA
    coherence : congLink (B².lnk (B²prod PA PA)) PA.lnk neutralMap ≡ Hom+ A
    coherence = {!!}
-}
