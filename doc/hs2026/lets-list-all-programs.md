# Abstract

To be written last...

# Introduction

```include
sections/Section0.md
```

# Simply-Typed Lambda Calculus

```include
sections/Section1.md
```

# System Fω

```include
sections/Section2.md
```

# Dependent Lambda Calculus

```include
sections/Section3.md
```

# Simply-Typed Linear Lambda Calculus

```include
sections/Section4.md
```

<!------------------------------------------------------------------------------

This is the main function for the test suite defined in `index.cabal`.

```haskell
import           Control.Enumerable (Enumerable)
import           Control.Search (search')
import qualified Control.Search as Search (Options (..))
import           Data.Coolean (Cool, Coolean (..), (&&&))
import           Data.Foldable (traverse_)
import qualified Options.Applicative as O
import           Section1 (S (..), Z, Pretty (..), pretty, nil)
import qualified Section1 as STLC
import qualified Section2 as SystemFw
import qualified Section3 as LambdaPi
import qualified Section4 as STLLC
```

```haskell
data Command
    = Count
    | List
    deriving (Read, Show)
```

```haskell
data System
    = STLC
    | SystemFw
    | LambdaPi
    | STLLC
    deriving (Read, Show)
```

```haskell
data Options = Options
    {  command  :: Command
    ,  depth    :: Int
    ,  system   :: System
    ,  pcs      :: Search.Options
    }
```

```haskell
options :: O.ParserInfo Options
options = O.info (optionsParser O.<**> O.helper) mempty
 where
  optionsParser :: O.Parser Options
  optionsParser =
      Options
          <$> commandParser
          <*> O.option O.auto (O.short 'd' <> O.value 10)
          <*> O.option O.auto (O.short 's' <> O.value STLC)
          <*> O.option O.auto (O.long "pcs" <> O.value Search.OF)

  commandParser :: O.Parser Command
  commandParser = O.subparser . mconcat $
    [ O.command "count"
        (O.info (pure Count) mempty)
    , O.command "list"
        (O.info (pure List) mempty)
    ]
```

```haskell
main :: IO ()
main = do
    Options{..} <- O.customExecParser (O.prefs O.subparserInline) options
    let searcher :: (Enumerable a) => (a -> Cool) -> IO [a]
        searcher = search' pcs depth
    let producer = case system of
            STLC -> do
                let τ = STLC.TyIota STLC.:-> STLC.TyIota
                fmap pretty <$> searcher (\e -> STLC.check nil e τ)
            SystemFw -> do
                let τ = SystemFw.TyAll SystemFw.Star (SystemFw.TyVar FZ SystemFw.:-> SystemFw.TyVar FZ)
                fmap pretty <$> searcher (\e -> SystemFw.checkTm nil nil e τ)
            LambdaPi -> do
                let τ = LambdaPi.mkPi LambdaPi.Star (LambdaPi.mkPi (LambdaPi.Var FZ) (LambdaPi.Var (FS FZ)))
                fmap pretty <$> searcher (\e -> LambdaPi.check nil e τ)
            STLLC -> do
                let τ = STLC.TyIota STLC.:-> STLC.TyIota
                fmap pretty <$> searcher (\e -> STLC.check nil e τ &&& snd (STLLC.checkUse e))
    let consumer = case command of
            Count -> print . length
            List  -> traverse_ putStrLn
    consumer =<< producer
```

------------------------------------------------------------------------------->
