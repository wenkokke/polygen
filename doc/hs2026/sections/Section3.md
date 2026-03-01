<!-- Dependent Lambda Calculus -->

<!------------------------------------------------------------------------------

```haskell
module Section3 where
```

------------------------------------------------------------------------------->

<!------------------------------------------------------------------------------

```haskell
import Control.Enumerable
import Control.Search
import Data.Coolean
import Data.Kind (Type)
import Section1 (Z, S (..), nil, (|>))
import Section1 (Name, Names, Pretty (..), app_prec, arr_prec, lam_prec, pretty, xyzws)
import Section2 (Norm (..), Neut (..), weak)
import Section2 (all_prec)
```

------------------------------------------------------------------------------->

Annotations in \hsannword.

```haskell
type Ty n = Tm n
```

```haskell
data Tm n
  =  Var   ({-"\field{x}"-} n)                                                                                                                -- x
  |  Lam   ({-"\field{e}"-} Tm (S n))                                                                                                         -- \lambda x.e
  |  App   ({-"\field{e}"-} Tm n) ({-"\field{e^\prime}"-} Tm n) ({-"\field{\tau}"-} Norm (Ty n)) ({-"\field{\tau^\prime}"-} Norm (Ty (S n)))  -- e^{\forall{x^\tau}.\tau^\prime}\;e^\prime
  |  Star                                                                                                                                     -- \star
  |  Pi    ({-"\field{\rho}"-} Ty n) ({-"\field{\rho^\prime}"-} Ty (S n)) ({-"\field{\tau}"-} Norm (Ty n))                                    -- \forall{x^\rho}.\rho^\prime
```

<!------------------------------------------------------------------------------

```haskell
deriving instance Eq n => Eq (Tm n)
deriving instance Show n => Show (Tm n)
deriving instance Functor Tm
```

```haskell
instance Enumerable n => Enumerable (Tm n) where
  enumerate = share . aconcat $
    [  pay $  c1 Var
    ,  pay $  c1 Lam
    ,  pay $  c4 App
    ,  pay $  c0 Star
    ,  pay $  c3 Pi
    ]
```

```haskell
instance Enumerable n => Enumerable (Norm (Tm n)) where
  enumerate = share . aconcat $
    [  pay .  c1 $ \(MkNorm v)                     ->  MkNorm (Lam v)
    ,  pay .  c0 $                                     MkNorm Star
    ,  pay .  c2 $ \(MkNorm τ)  (MkNorm τ')        ->  MkNorm (Pi τ τ' (MkNorm τ))
    ,         c1 $ \(MkNeut n)                     ->  MkNorm n
    ]
```

```haskell
instance Enumerable n => Enumerable (Neut (Tm n)) where
  enumerate = share . aconcat $
    [  pay .  c1 $ \x                              ->  MkNeut (Var x)
    ,  pay .  c4 $ \(MkNeut n)  (MkNorm v)  τ  τ'  ->  MkNeut (App n v τ τ')
    ]
```

------------------------------------------------------------------------------->

<!------------------------------------------------------------------------------

```haskell
mkPi :: ({-"\field{\tau}"-} Ty n) -> ({-"\field{\tau^\prime}"-} Ty (S n)) -> Tm n
mkPi τ τ' = Pi τ τ' (MkNorm τ)
```

------------------------------------------------------------------------------->

```haskell
type Sub n n' = n -> Tm n'
```

```haskell
ε :: Sub n n
ε = Var
```

```haskell
sub :: Sub n n' -> Tm n -> Tm n'
sub σ = \case
  Var   i          -> σ i
  Lam   e          -> Lam  (sub (weak σ |> Var FZ) e)
  App   e e' τ τ'  -> App  (sub σ e) (sub σ e') (sub σ <$> τ) (sub (weak σ |> Var FZ) <$> τ')
  Star             -> Star
  Pi    ρ ρ' τ     -> Pi   (sub σ ρ) (sub (weak σ |> Var FZ) ρ') (sub σ <$> τ)
```

```haskell
step :: Tm n -> Maybe (Tm n)
step = \case
  App (Lam e) e' τ τ'  ->   Just (sub (ε |> e') e)
  Var   i              ->   Nothing
  Lam   e              ->   Lam  <$> step  e
  App   e e' τ τ'      ->   App  <$> step  e  <*> pure  e'  <*> pure τ <*> pure τ'
                       <|>  App  <$> pure  e  <*> step  e'  <*> pure τ <*> pure τ'
  Star                 ->   Nothing
  Pi    ρ ρ' τ         ->   Pi   <$> step  ρ  <*> pure  ρ'  <*> pure τ
                       <|>  Pi   <$> pure  ρ  <*> step  ρ'  <*> pure τ
```

```haskellspec
norm :: Tm n -> Norm (Tm n)
norm e = maybe (MkNorm e) norm (step e)
```

<!------------------------------------------------------------------------------

```haskell
norm :: (Eq n) => Tm n -> Norm (Tm n)
norm ρ = maybe (MkNorm ρ) norm (safe step ρ)
 where
  safe :: (Eq a) => (a -> Maybe a) -> a -> Maybe a
  safe f x = f x >>= \y -> if x == y then (error "BOOM") else Just y
```

------------------------------------------------------------------------------->

```haskell
type Tys n = n -> Ty n
```

```haskell
check :: (Eq n) => Tys n -> Tm n -> Ty n -> Cool
check γ  (Var  i)                            τ            =    toCool (γ i == τ)
check γ  (Lam  e)                            (Pi τ τ' _)  =    check (weak (γ |> τ)) e τ'
check γ  (App  e e' (MkNorm τ) (MkNorm τ'))  τ''          =    check γ (Pi τ τ' (MkNorm τ)) Star
                                                          !&&  check γ e' τ
                                                          !&&  toCool (norm (sub (ε |> e') τ') == MkNorm τ'')
                                                          !&&  check γ e (Pi τ τ' (MkNorm τ))
check γ  Star                                Star         =    true
check γ  (Pi ρ ρ' (MkNorm τ))                Star         =    check γ ρ Star
                                                          !&&  toCool (norm ρ == MkNorm τ)
                                                          !&&  check (weak (γ |> Star)) ρ' Star
check _  _                                   _            =    false
```

```{=latex}
\setlength{\arraycolsep}{3pt}
\[\!\!%
\begin{array}{llll}
\lambda \alpha . \lambda x . x &
\lambda \alpha . \lambda x . (\lambda y . x)^{\forall \beta^{\star } . \alpha} \; (\forall \gamma^{\alpha} . \gamma) &
\lambda \alpha . \lambda x . (\lambda y . x)^{\forall \beta^{\forall \gamma^{\alpha} . \alpha} . \alpha} \; (\lambda z . z) &
\\
\lambda \alpha . \lambda x . (\lambda y . y)^{\forall \beta^{\alpha} . \alpha} \; x &
\lambda \alpha . \lambda x . (\lambda y . x)^{\forall \beta^{\star } . \alpha} \; (\forall \gamma^{\alpha} . \alpha) &
\lambda \alpha . \lambda x . (\lambda y . x)^{\forall \beta^{\forall \gamma^{\alpha} . \alpha} . \alpha} \; (\lambda z . x) &
\\
\lambda \alpha . \lambda x . (\lambda y . x)^{\forall \beta^{\alpha} . \alpha} \; x &
\lambda \alpha . \lambda x . (\lambda y . x)^{\forall \beta^{\star } . \alpha} \; (\forall \gamma^{\alpha} . \star) &
\lambda \alpha . \lambda x . (\lambda y . x)^{\forall \beta^{\forall \gamma^{\alpha} . \star } . \alpha} \; (\lambda z . \alpha) &
\\
\lambda \alpha . \lambda x . (\lambda y . x)^{\forall \beta^{\star } . \alpha} \; \alpha &
\lambda \alpha . \lambda x . (\lambda y . x)^{\forall \beta^{\star } . \alpha} \; (\forall \gamma^{\star } . \gamma) &
\lambda \alpha . \lambda x . (\lambda y . x)^{\forall \beta^{\forall \gamma^{\alpha} . \star } . \alpha} \; (\lambda z . \star ) &
\\
\lambda \alpha . \lambda x . (\lambda y . x)^{\forall \beta^{\star } . \alpha} \; \star &
\lambda \alpha . \lambda x . (\lambda y . x)^{\forall \beta^{\star } . \alpha} \; (\forall \gamma^{\star } . \alpha) &
\lambda \alpha . \lambda x . (\lambda y . x)^{\forall \beta^{\forall \gamma^{\star } . \alpha} . \alpha} \; (\lambda z . x) &
\\
\lambda \alpha . (\lambda x . \lambda y . y)^{\forall \beta^{\star } . \forall \gamma^{\beta} . \beta} \; \alpha &
\lambda \alpha . \lambda x . (\lambda y . x)^{\forall \beta^{\star } . \alpha} \; (\forall \gamma^{\star } . \star) &
\lambda \alpha . \lambda x . (\lambda y . x)^{\forall \beta^{\forall \gamma^{\star } . \star } . \alpha} \; (\lambda z . z) &
\\
\lambda \alpha . (\lambda x . \lambda y . y)^{\forall \beta^{\star } . \forall \gamma^{\alpha} . \alpha} \; \alpha &
&
\lambda \alpha . \lambda x . (\lambda y . x)^{\forall \beta^{\forall \gamma^{\star } . \star } . \alpha} \; (\lambda z . \alpha) &
\\
\lambda \alpha . (\lambda x . \lambda y . y)^{\forall \beta^{\star } . \forall \gamma^{\alpha} . \alpha} \; \star &
&
\lambda \alpha . \lambda x . (\lambda y . x)^{\forall \beta^{\forall \gamma^{\star } . \star } . \alpha} \; (\lambda z . \star ) &
\end{array}
\]
```

<!------------------------------------------------------------------------------










------------------------------------------------------------------------------->


<!------------------------------------------------------------------------------

# Pretty Printer

```haskell
showsPrecTm :: Int -> [Name] -> Names n -> Tm n -> (ShowS, [Name])
showsPrecTm p fresh γ = \case
  Var x ->
    (shows_var_x, fresh)
    where
    shows_var_x = showString (γ x)
  Lam e ->
    (showParen (p > lam_prec) shows_lam_e, fresh2)
    where
    (x : fresh1) = fresh
    (shows_e, fresh2) = showsPrecTm lam_prec fresh1 (γ |> x) e
    shows_lam_e = showString ("\\lambda " <> x <> " . ") . shows_e
  App e e' (MkNorm τ) (MkNorm τ') ->
    (showParen (p > app_prec) shows_app_e_e', fresh3)
    where
    (shows_e, fresh1) = showsPrecTm app_prec fresh γ e
    (shows_pi_τ_τ', fresh2) = showsPrecTm all_prec fresh1 γ (mkPi τ τ')
    (shows_e', fresh3) = showsPrecTm (app_prec + 1) fresh2 γ e'
    shows_app_e_e' = shows_e . showString "^{" . shows_pi_τ_τ' . showString "} \\; " . shows_e'
  Star ->
    (shows_star, fresh)
    where
    shows_star = (showString "\\star ")
  Pi ρ ρ' _ ->
    (shows_all_ρ_ρ', fresh3)
    where
    (x : fresh1) = fresh
    (shows_ρ, fresh2) = showsPrecTm all_prec fresh1 γ ρ
    (shows_ρ', fresh3) = showsPrecTm all_prec fresh2 (γ |> x) ρ'
    shows_all_ρ_ρ' = showString "\\forall " . showString x . showString "^{" . shows_ρ . showString "} . " . shows_ρ'

```

```haskell
instance Show (Pretty (Tm Z)) where
  showsPrec :: Int -> Pretty (Tm Z) -> ShowS
  showsPrec p (Pretty e) = fst (showsPrecTm p xyzws nil e)
```

------------------------------------------------------------------------------->
