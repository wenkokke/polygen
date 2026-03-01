<!-- Linear Lambda Calculus -->

<!------------------------------------------------------------------------------

```haskell
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternGuards #-}
```

```haskell
module Section4 where
```

```haskell
import Control.Enumerable
import Control.Search
import Data.Coolean
import Section1 (S (..), Z, Ty (..), Tm (..), nil)
```

------------------------------------------------------------------------------->

```haskell
data Use = None | Once | Many
```

<!------------------------------------------------------------------------------

```haskell
deriving instance Eq Use
deriving instance Show Use
```

------------------------------------------------------------------------------->

```haskell
instance Semigroup Use where
  None  <>  u     = u
  u     <>  None  = u
  Once  <>  Once  = Many
  Many  <>  u     = Many
  u     <>  Many  = Many
```

```haskell
instance Monoid Use where
  mempty = None
```

```haskell
data Uses n where
  Nil   ::                   Uses Z
  (:>)  :: Uses n -> Use ->  Uses (S n)
```

```haskell
instance Semigroup (Uses n) where
  Nil      <>  Nil      = Nil
  us :> u  <>  vs :> v  = (us <> vs) :> (u <> v)
```

```haskell
class MkUses n where
  never   :: Uses n
  once    :: n -> Uses n
```

```haskell
instance MkUses Z where
  once    = nil
  never   = Nil
```

```haskell
instance (MkUses n) => MkUses (S n) where
  never   = never :> None
  once    = \case{FZ -> never :> Once; FS i -> once i :> None}
```

```haskell
instance (MkUses n) => Monoid (Uses n) where
  mempty = never
```

```haskell
checkUse :: (MkUses n) => Tm n -> (Uses n, Cool)
checkUse = \case
  Var x -> (once x, true)
  Lam e | (us :> u, eOk) <- checkUse e -> (us, eOk &&& u == Once)
  App e e' _ -> (&&&) <$> checkUse e <*> checkUse e'
```
