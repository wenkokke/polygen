<!-- Simply-Typed Lambda Calculus -->

<!------------------------------------------------------------------------------

```haskell
module Section1 where
```

------------------------------------------------------------------------------->

```haskell
import Control.Enumerable
import Control.Search
import Data.Coolean
```

<!------------------------------------------------------------------------------


```haskell
import Data.Bits
import Data.Foldable (traverse_)
import Data.List (transpose)
import Data.Proxy (Proxy (..))
import Debug.Trace (traceShow)
import qualified Options.Applicative as O
import Prelude hiding (lookup)
import Text.Printf (printf)
```

------------------------------------------------------------------------------->

```haskell
data Z
data S n = FZ | FS n
```

<!------------------------------------------------------------------------------

```haskell
deriving instance Eq Z
deriving instance Eq n => Eq (S n)
deriving instance Functor S
deriving instance Show Z
deriving instance Show n => Show (S n)
```

------------------------------------------------------------------------------->

```haskell
instance Enumerable Z where
  enumerate = share empty

instance Enumerable n => Enumerable (S n) where
  enumerate = share . aconcat $ [c0 FZ, c1 FS]
```

```haskell
data Ty
  =  TyIota                                                      -- \iota
  |  ({-"\field{\tau}"-} Ty) :-> ({-"\field{\tau^\prime}"-} Ty)  -- \tau\rightarrow\tau^\prime
```

<!------------------------------------------------------------------------------

```haskell
deriving instance Eq Ty
deriving instance Show Ty
deriveEnumerable ''Ty
```

------------------------------------------------------------------------------->

```haskell
data Tm n
  =  Var  ({-"\field{x}"-} n)                                                            -- x
  |  Lam  ({-"\field{e}"-} Tm (S n))                                                     -- \lambda x.e
  |  App  ({-"\field{e}"-} Tm n)  ({-"\field{e^\prime}"-} Tm n) ({-"\field{\tau}"-} Ty)  -- e \; e^{\prime\tau}
```

<!------------------------------------------------------------------------------

```haskell
deriving instance Eq n => Eq (Tm n)
deriving instance Show n => Show (Tm n)
deriveEnumerable ''Tm
```

------------------------------------------------------------------------------->

```haskell
type Tys n = n -> Ty
```

```haskell
nil :: Z -> a
nil n = case n of {}
```

```haskell
(|>) :: (n -> a) -> a -> (S n -> a)
(fs |> fz) FZ      = fz
(fs |> fz) (FS n)  = fs n
```

```haskell
check :: Tys n -> Tm n -> Ty -> Cool
check γ  (Var x)       τ           =  toCool (γ x == τ)
check γ  (App e e' τ)  τ'          =  check γ e (τ :-> τ') &&& check γ e' τ
check γ  (Lam e)       (τ :-> τ')  =  check (γ |> τ) e τ'
check _  _             _           =  false
```

```haskell
enumTmZ :: Int -> Ty -> IO [Tm Z]
enumTmZ depth τ = search depth (\e -> check nil e τ)
```

```{=latex}
\setlength{\arraycolsep}{3pt}
\[\!\!%
\begin{array}{llll}
\lambda x . x &
\lambda x . (\lambda y . y) \; x^{ \bot } &
\lambda x . (\lambda y . y) \; ((\lambda z . z) \; x^{ \bot })^{ \bot } &
\lambda x . (\lambda y . y) \; ((\lambda z . x) \; x^{ \bot })^{ \bot } \\
\lambda x . (\lambda y . x) \; x^{ \bot } &
\lambda x . (\lambda y . x) \; (\lambda z . z)^{( \bot  \rightarrow  \bot )} &
\lambda x . (\lambda y . x) \; (\lambda z . x)^{( \bot  \rightarrow  \bot )} &
\lambda x . (\lambda y . x) \; ((\lambda z . z) \; x^{ \bot })^{ \bot } \\
\lambda x . (\lambda y . x) \; ((\lambda z . x) \; x^{ \bot })^{ \bot } &
\lambda x . (\lambda y . (\lambda z . z) \; y^{ \bot }) \; x^{ \bot } &
\lambda x . (\lambda y . (\lambda z . z) \; x^{ \bot }) \; x^{ \bot } &
\lambda x . (\lambda y . (\lambda z . y) \; y^{ \bot }) \; x^{ \bot } \\
\lambda x . (\lambda y . (\lambda z . y) \; x^{ \bot }) \; x^{ \bot } &
\lambda x . (\lambda y . (\lambda z . x) \; y^{ \bot }) \; x^{ \bot } &
\lambda x . (\lambda y . (\lambda z . x) \; x^{ \bot }) \; x^{ \bot } &
\lambda x . (\lambda y . \lambda z . z) \; x^{ \bot } \; x^{ \bot } \\
\lambda x . (\lambda y . \lambda z . y) \; x^{ \bot } \; x^{ \bot } &
\lambda x . (\lambda y . \lambda z . x) \; x^{ \bot } \; x^{ \bot } &
(\lambda x . x) \; (\lambda y . y)^{( \bot  \rightarrow  \bot )} &
(\lambda x . \lambda y . y) \; (\lambda z . z)^{( \bot  \rightarrow  \bot )}
\end{array}
\]
```

<!------------------------------------------------------------------------------

# Pretty Printer

```haskell
type Name = String
```

```haskell
xyzws :: [Name]
xyzws = concat . transpose $ [xs, ys, zs, ws]
 where
  xs = "x" : ["x_{" <> show i <> "}" | i <- [1..]]
  ys = "y" : ["y_{" <> show i <> "}" | i <- [1..]]
  zs = "z" : ["z_{" <> show i <> "}" | i <- [1..]]
  ws = "w" : ["w_{" <> show i <> "}" | i <- [1..]]
```

```haskell
type Names n = n -> Name
```

```haskell
arr_prec, lam_prec, app_prec :: Int
arr_prec = 2
lam_prec = 10
app_prec = 11
```

```haskell
showsPrecTy :: Int -> Ty -> ShowS
showsPrecTy p = \case
  TyIota   -> showString " \\iota "
  τ :-> τ' -> showParen (p > arr_prec) shows_τ_arr_τ'
   where
    shows_τ  = showsPrecTy (arr_prec + 1) τ
    shows_τ' = showsPrecTy arr_prec τ'
    shows_τ_arr_τ' = shows_τ . showString " \\rightarrow " . shows_τ'
```

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
  App e e' τ ->
    (showParen (p > app_prec) shows_app_e_e', fresh2)
    where
    (shows_e, fresh1) = showsPrecTm app_prec fresh γ e
    (shows_e', fresh2) = showsPrecTm (app_prec + 1) fresh1 γ e'
    shows_τ = showsPrecTy (app_prec + 1) τ
    shows_app_e_e' = shows_e . showString " \\; " . shows_e' . showString "^{" . shows_τ . showString "}"
```

```haskell
newtype Pretty a = Pretty a

pretty :: Show (Pretty a) => a -> String
pretty = show . Pretty

instance Show (Pretty (Tm Z)) where
  showsPrec :: Int -> Pretty (Tm Z) -> ShowS
  showsPrec p (Pretty e) = fst (showsPrecTm p xyzws nil e)
```

------------------------------------------------------------------------------->
