<!-- System Fω -->

<!------------------------------------------------------------------------------

```haskell
module Section2 where
```

------------------------------------------------------------------------------->

<!------------------------------------------------------------------------------

```haskell
import           Control.Enumerable
import           Control.Search
import           Data.Coolean hiding ((!&&))
import qualified Data.Coolean as Cool
import           Data.List (transpose)
import           Data.Monoid (Any (..), Sum (..))
import           Section1 (Z, S (..), nil, (|>))
import           Section1 (Name, Names, Pretty (..), app_prec, arr_prec, lam_prec, pretty, xyzws)
```

This is intended to import (!&&) with a fixity.

```haskell
infixl 2 !&&

(!&&) :: (Coolean a, Coolean b) => a -> b -> Cool
(!&&) = (Cool.!&&)
```

------------------------------------------------------------------------------->

```haskell
data Ki
  =  Star                                                            -- \star
  |  ({-"\field{\kappa}"-} Ki) :=> ({-"\field{\kappa^\prime}"-} Ki)  -- \kappa\Rightarrow\kappa^\prime
```

<!------------------------------------------------------------------------------

```haskell
deriving instance Eq Ki
deriving instance Show Ki
deriveEnumerable ''Ki
```

------------------------------------------------------------------------------->

```haskell
data  Ty m
   =  ({-"\field{\rho}"-} Ty m) :-> ({-"\field{\rho^\prime}"-} Ty m)                                -- \rho\rightarrow\rho^\prime
   |  TyVar  ({-"\field{\alpha}"-} m)                                                               -- \alpha
   |  TyLam  ({-"\field{\rho}"-} Ty (S m))                                                          -- \lambda x.\rho
   |  TyApp  ({-"\field{\rho}"-} Ty m) ({-"\field{\rho^\prime}"-} Ty m) ({-"\field{\kappa}"-}  Ki)  -- \rho\;\rho^{\prime\kappa}
   |  TyAll  ({-"\field{\kappa}"-} Ki) ({-"\field{\rho}"-} Ty (S m))                                -- \forall \alpha^{\kappa}.\rho
```

<!------------------------------------------------------------------------------

```haskell
deriving instance Eq m => Eq (Ty m)
deriving instance Functor Ty
deriving instance Show m => Show (Ty m)
deriveEnumerable ''Ty
```

------------------------------------------------------------------------------->

```haskell
type Kis m = m -> Ki
```

```haskell
checkTy :: Kis m -> Ty m -> Ki -> Cool
checkTy δ  (TyVar α)       κ           = toCool (δ α == κ)
checkTy δ  (TyLam ρ)       (κ :=> κ')  = checkTy (δ |> κ) ρ κ'
checkTy δ  (TyApp ρ ρ' κ)  κ'          = checkTy δ ρ (κ :=> κ') &&& checkTy δ ρ' κ
checkTy δ  (ρ :-> ρ')      Star        = checkTy δ ρ Star &&& checkTy δ ρ' Star
checkTy δ  (TyAll κ ρ)     Star        = checkTy (δ |> κ) ρ Star
checkTy _  _               _           = false
```

```{=latex}
\inlinehs%
\begin{mathpar}
\mbox{%
```
```haskell
newtype Norm  a =  {-"\Varid{MkNorm}\;"-}  MkNorm  a
```
```{=latex}
}
and
\mbox{%
```
```haskell
newtype Neut  a =  {-"\Varid{MkNeut}\;"-}  MkNeut  a
```
```{=latex}
}
\end{mathpar}
\plainhs%
```

<!------------------------------------------------------------------------------

```haskell
instance Enumerable m => Enumerable (Norm (Ty m)) where
  enumerate = share . aconcat $
    [       c1 $ \(MkNeut n) -> MkNorm n
    , pay . c1 $ \(MkNorm τ) -> MkNorm (TyLam τ)
    ]

instance Enumerable m => Enumerable (Neut (Ty m)) where
  enumerate = share . aconcat . fmap pay $
    [  c2  $ \(MkNeut n) (MkNeut n')  -> MkNeut (n :-> n')
    ,  c2  $ \κ          (MkNeut n)   -> MkNeut (TyAll κ n)
    ,  c1  $ \α                       -> MkNeut (TyVar α)
    ,  c3  $ \(MkNeut n) (MkNorm t) κ -> MkNeut (TyApp n t κ)
    ]
```

------------------------------------------------------------------------------->

<!------------------------------------------------------------------------------

```haskell
deriving instance Eq a => Eq (Norm a)
deriving instance Eq a => Eq (Neut a)
deriving instance Functor Norm
deriving instance Functor Neut
deriving instance Show a => Show (Norm a)
deriving instance Show a => Show (Neut a)
```

------------------------------------------------------------------------------->

```haskell
data Tm m n
  =  Var  ({-"\field{x}"-} n)                                                                                                              -- x
  |  Lam  ({-"\field{e}"-} Tm m (S n))                                                                                                     -- \lambda x.e
  |  App  ({-"\field{e}"-} Tm m n) ({-"\field{e^\prime}"-} Tm m n) ({-"\field{\tau}"-} Norm (Ty m))                                        -- e\;e^{\prime\tau}
  |  LAM  ({-"\field{e}"-} Tm (S m) n)                                                                                                     -- \Lambda \alpha.e
  |  APP  ({-"\field{e}"-} Tm m n) ({-"\field{\kappa}"-} Ki) ({-"\field{\tau}"-} Norm (Ty (S m))) ({-"\field{\tau^\prime}"-} Norm (Ty m))  -- e^{\forall \alpha^\kappa.\tau}\;\tau^\prime
```

<!------------------------------------------------------------------------------

```haskell
deriving instance (Eq m, Eq n) => Eq (Tm m n)
deriving instance (Show m, Show n) => Show (Tm m n)
deriveEnumerable ''Tm
```

------------------------------------------------------------------------------->

```haskell
type TySub m m' = m -> Ty m'
```

```haskell
ε :: TySub m m
ε = TyVar
```

```haskell
weak :: (Functor f) => (m -> f n) -> (m -> f (S n))
weak σ = fmap FS . σ
```

```haskell
sub :: TySub m m' -> Ty m -> Ty m'
sub σ = \case
  TyVar α       -> σ α
  TyLam ρ       -> TyLam (sub (weak σ |> TyVar FZ) ρ)
  TyApp ρ ρ' κ  -> TyApp (sub σ ρ) (sub σ ρ') κ
  ρ :-> ρ'      -> sub σ ρ :-> sub σ ρ'
  TyAll κ ρ     -> TyAll κ (sub (weak σ |> TyVar FZ) ρ)
```


```haskell
step :: Ty m -> Maybe (Ty m)
step = \case
  TyApp (TyLam ρ) ρ' κ  ->   pure (sub (ε |> ρ') ρ)
  TyVar α               ->   empty
  TyLam ρ               ->   TyLam  <$>  step  ρ
  TyApp ρ ρ' κ          ->   TyApp  <$>  step  ρ  <*>  pure  ρ'  <*> pure κ
                        <|>  TyApp  <$>  pure  ρ  <*>  step  ρ'  <*> pure κ
  ρ :-> ρ'              ->   (:->)  <$>  step  ρ  <*>  pure  ρ'
                        <|>  (:->)  <$>  pure  ρ  <*>  step  ρ'
  TyAll κ ρ             ->   TyAll  <$>  pure  κ  <*>  step  ρ
```

```haskellspec
norm :: Ty m -> Norm (Ty m)
norm ρ = maybe (MkNorm ρ) norm (step ρ)
```

<!------------------------------------------------------------------------------

```haskell
norm :: (Eq m) => Ty m -> Norm (Ty m)
norm ρ = maybe (MkNorm ρ) norm (safe step ρ)
 where
  safe :: (Eq a) => (a -> Maybe a) -> a -> Maybe a
  safe f x = f x >>= \y -> if x == y then (error "BOOM") else Just y
```

------------------------------------------------------------------------------->

```haskell
type Tys m n = n -> Ty m
```

```haskell
checkTm :: (Eq m) => Kis m -> Tys m n -> Tm m n -> Ty m -> Cool
checkTm δ γ  (Var x)                           τ            =    toCool (γ x == τ)
checkTm δ γ  (Lam e)                           (τ :-> τ')   =    checkTm δ (γ |> τ) e τ'
checkTm δ γ  (App f e (MkNorm τ))              τ'           =    checkTy δ τ Star
                                                            !&&  checkTm δ γ f (τ :-> τ') &&&  checkTm δ γ e τ
checkTm δ γ  (LAM e)                           (TyAll κ τ)  =    checkTm (δ |> κ) (weak γ) e τ
checkTm δ γ  (APP e κ (MkNorm τ) (MkNorm τ'))  τ''          =    checkTy δ (TyAll κ τ) Star &&&  checkTy δ τ' κ
                                                            !&&  checkTm δ γ e (TyAll κ τ) &&&  norm (sub (ε |> τ') τ) == MkNorm τ''
checkTm _ _  _                                 _            =    false
```

```haskell
loop :: Tm Z Z
loop = APP (LAM (Lam (Var FZ))) Star (MkNorm α_α) (MkNorm ω)
 where
  α_α :: Ty (S Z)
  α_α = TyApp (TyVar FZ) (TyVar FZ) Star

  ω :: Ty Z
  ω = TyLam (TyApp (TyVar FZ) (TyVar FZ) Star)
```

```{=latex}
\setlength{\arraycolsep}{3pt}
\[\!\!%
\begin{array}{llll}
\Lambda \alpha . \lambda x.x &
\Lambda \alpha . (\lambda x.\lambda y.y) (\lambda z.z)^{(\alpha \rightarrow \alpha)} &
\Lambda \alpha . \lambda x.(\Lambda \beta . x)^{(\forall \alpha_{1}^{ \star } . \alpha)} (\forall \beta_{1}^{ \star } . \beta_{1}) &
\\
\Lambda \alpha . \lambda x.(\lambda y.y) x^{\alpha} &
\Lambda \alpha . \lambda x.(\lambda y.x) (\lambda z.z)^{(\alpha \rightarrow \alpha)} &
\Lambda \alpha . \lambda x.(\Lambda \beta . x)^{(\forall \alpha_{1}^{ \star } . \alpha)} (\forall \beta_{1}^{ \star } . \alpha) &
\\
\Lambda \alpha . \lambda x.(\lambda y.x) x^{\alpha} &
\Lambda \alpha . \lambda x.(\lambda y.x) (\lambda z.x)^{(\alpha \rightarrow \alpha)} &
\Lambda \alpha . \lambda x.(\Lambda \beta . x)^{(\forall \alpha_{1}^{ \star } . \alpha)} (\alpha \rightarrow \alpha) &
\\
\Lambda \alpha . (\lambda x.x) (\lambda y.y)^{(\alpha \rightarrow \alpha)} &
\Lambda \alpha . \lambda x.(\lambda y.x) (\Lambda \beta . x)^{(\forall \alpha_{1}^{ \star } . \alpha)} &
\Lambda \alpha . (\Lambda \beta . \lambda x.x)^{(\forall \alpha_{1}^{ \star } . (\alpha_{1} \rightarrow \alpha_{1}))} \alpha &
\\
\Lambda \alpha . \lambda x.(\Lambda \beta . x)^{(\forall \alpha_{1}^{ \star } . \alpha)} \alpha &
\Lambda \alpha . (\Lambda \beta . \lambda x.x)^{(\forall \alpha_{1}^{ \star } . (\alpha \rightarrow \alpha))} \alpha &
\end{array}
\]
```

<!------------------------------------------------------------------------------

# Pretty Printer

```haskell
showsPrecKi :: Int -> Ki -> ShowS
showsPrecKi p = \case
  Star     -> showString " \\star "
  κ :=> κ' -> showParen (p > arr_prec) shows_κ_arr_κ'
   where
    shows_κ  = showsPrecKi (arr_prec + 1) κ
    shows_κ' = showsPrecKi arr_prec κ'
    shows_κ_arr_κ' = shows_κ . showString " \\Rightarrow " . shows_κ'
```

```haskell
αβs :: [Name]
αβs = concat . transpose $ [αs, βs]
 where
  αs = "\\alpha" : ["\\alpha_{" <> show i <> "}" | i <- [1..]]
  βs = "\\beta" : ["\\beta_{" <> show i <> "}" | i <- [1..]]
```

```haskell
all_prec :: Int
all_prec = 9
```

```haskell
showsPrecTy :: Int -> [Name] -> Names m -> Ty m -> (ShowS, [Name])
showsPrecTy p fresh δ = \case
  TyVar α ->
    (shows_var_α, fresh)
    where
    shows_var_α = showString (δ α)
  TyLam ρ ->
    (showParen (p > lam_prec) shows_lam_ρ, fresh2)
    where
    (α : fresh1) = fresh
    (shows_ρ, fresh2) = showsPrecTy lam_prec fresh1 (δ |> α) ρ
    shows_lam_ρ = showString ("\\lambda " <> α <> " . ") . shows_ρ
  TyApp ρ ρ' κ ->
    (showParen (p > app_prec) shows_app_ρ_ρ', fresh2)
    where
    (shows_ρ, fresh1) = showsPrecTy app_prec fresh δ ρ
    (shows_ρ', fresh2) = showsPrecTy (app_prec + 1) fresh1 δ ρ'
    shows_κ = showsPrecKi (app_prec + 1) κ
    shows_app_ρ_ρ' = shows_ρ . showString " " . shows_ρ' . showString "^{" . shows_κ . showString "}"
  ρ :-> ρ' ->
    (showParen (p > arr_prec) shows_ρ_arr_ρ', fresh2)
    where
    (shows_ρ, fresh1) = showsPrecTy (arr_prec + 1) fresh δ ρ
    (shows_ρ', fresh2) = showsPrecTy arr_prec fresh1 δ ρ'
    shows_ρ_arr_ρ' = shows_ρ . showString " \\rightarrow " . shows_ρ'
  TyAll κ ρ ->
    (showParen (p > all_prec) shows_all_ρ, fresh2)
    where
    (α : fresh1) = fresh
    shows_κ = showsPrecKi (all_prec + 1) κ
    (shows_ρ, fresh2) = showsPrecTy all_prec fresh1 (δ |> α) ρ
    shows_all_ρ = showString "\\forall " . showString α . showString "^{" . shows_κ . showString "} . " . shows_ρ
```

```haskell
showsPrecTm :: Int -> [Name] -> [Name] -> Names m -> Names n -> Tm m n -> (ShowS, ([Name], [Name]))
showsPrecTm p freshTy freshTm δ γ = \case
  Var x ->
    (shows_var_x, (freshTy, freshTm))
    where
    shows_var_x = showString (γ x)
  Lam e ->
    (showParen (p > lam_prec) shows_lam_e, (freshTy1, freshTm2))
    where
    (x : freshTm1) = freshTm
    (shows_e, (freshTy1, freshTm2)) = showsPrecTm lam_prec freshTy freshTm1 δ (γ |> x) e
    shows_lam_e = showString ("\\lambda " <> x <> ".") . shows_e
  App e e' (MkNorm τ) ->
    (showParen (p > app_prec) shows_app_e_e', (freshTy3, freshTm2))
    where
    (shows_e, (freshTy1, freshTm1)) = showsPrecTm app_prec freshTy freshTm δ γ e
    (shows_e', (freshTy2, freshTm2)) = showsPrecTm (app_prec + 1) freshTy1 freshTm1 δ γ e'
    (shows_τ, freshTy3) = showsPrecTy (app_prec + 1) freshTy2 δ τ
    shows_app_e_e' = shows_e . showString " " . shows_e' . showString "^{" . shows_τ . showString "}"
  LAM e ->
    (showParen (p > lam_prec) shows_LAM_e, (freshTy2, freshTm1))
    where
    (α : freshTy1) = freshTy
    (shows_e, (freshTy2, freshTm1)) = showsPrecTm lam_prec freshTy1 freshTm (δ |> α) γ e
    shows_LAM_e = showString ("\\Lambda " <> α <> " . ") . shows_e
  APP e κ (MkNorm τ) (MkNorm τ') ->
    (showParen (p > app_prec) shows_app_e_τ', (freshTy3, freshTm1))
   where
    (shows_e, (freshTy1, freshTm1)) = showsPrecTm (app_prec + 1) freshTy freshTm δ γ e
    (shows_all_α_κ_τ, freshTy2) = showsPrecTy (app_prec + 1) freshTy1 δ (TyAll κ τ)
    (shows_τ', freshTy3) = showsPrecTy (app_prec + 1) freshTy2 δ τ'
    shows_app_e_τ' = shows_e . showString "^{" . shows_all_α_κ_τ . showString "} " . shows_τ'
```

```haskell
instance Show (Pretty (Tm Z Z)) where
  showsPrec :: Int -> Pretty (Tm Z Z) -> ShowS
  showsPrec p (Pretty e) = fst (showsPrecTm p αβs xyzws nil nil e)
```

------------------------------------------------------------------------------->
