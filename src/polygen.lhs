\begin{comment}
\begin{code}
{-# LANGUAGE ApplicativeDo        #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE EmptyDataDeriving    #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
\end{code}
\end{comment}


\begin{comment}
\begin{code}
import Control.Enumerable
import Control.Search
import Control.Monad.Reader
import Data.Bifunctor
import Data.Bifunctor.TH
import Data.Coolean
import Data.Maybe
import System.Environment
\end{code}
\end{comment}


\subsection{Names}

\begin{code}
data Z
  deriving (Typeable, Eq, Read, Show)

instance Enumerable Z where
  enumerate = datatype []

fromZ :: Z -> a
fromZ z = case z of {}
\end{code}

\begin{code}
data S n
  = FZ
  | FS n
  deriving (Typeable, Eq, Read, Functor)

instance Enumerable n => Enumerable (S n) where
  enumerate = share $ aconcat
    [ c0 FZ
    , c1 FS
    ]
\end{code}

\begin{code}
class Fin n where
  toInt :: n -> Int

instance Fin Z where
  toInt = fromZ

instance Fin n => Fin (S n) where
  toInt FZ     = 0
  toInt (FS i) = succ (toInt i)

instance Fin (S n) => Show (S n) where
  show = show . toInt
\end{code}


\subsection{Kinds}

\begin{code}
infixr 9 :=>

data Kind
  = Star
  | Kind :=> Kind
  deriving (Typeable, Eq, Read, Show)

deriveEnumerable ''Kind
\end{code}


\subsection{Types}

\begin{code}
infixr 9 :->

data Type tyname
  = TyVoid
  | Type tyname :-> Type tyname
  | TyForall Kind (Type (S tyname))
  | TyVar tyname
  | TyLam (Type (S tyname))
  | TyApp (Type tyname) (Type tyname) Kind
  deriving (Typeable, Eq, Read, Show, Functor)

deriveEnumerable ''Type
\end{code}

\begin{code}
newtype Normal a = Normal { unNormal :: a }
  deriving (Typeable, Eq, Functor)

instance Show a => Show (Normal a) where
  showsPrec d a = showsPrec d (unNormal a)

instance Enumerable tyname => Enumerable (Normal (Type tyname)) where
  enumerate = share $ aconcat
    [        c1  $ \ty  ->  Normal (unNeutral ty)
    , pay .  c1  $ \ty  ->  Normal (TyLam (unNormal ty))
    ]
\end{code}

\begin{code}
newtype Neutral a = Neutral { unNeutral :: a }
  deriving (Typeable, Eq, Functor)

instance Show a => Show (Neutral a) where
  showsPrec d a = showsPrec d (unNeutral a)

instance Enumerable tyname => Enumerable (Neutral (Type tyname)) where
  enumerate = share $ aconcat
    [ pay .  c0  $                 Neutral TyVoid
    , pay .  c2  $ \ty1 ty2    ->  Neutral (unNeutral ty1 :-> unNeutral ty2)
    , pay .  c2  $ \k ty       ->  Neutral (TyForall k (unNeutral ty))
    , pay .  c1  $ \i          ->  Neutral (TyVar i)
    , pay .  c3  $ \ty1 ty2 k  ->  Neutral (TyApp (unNeutral ty1) (unNormal ty2) k)
    ]
\end{code}


\subsection{Kind Checking}

\begin{code}
type KindEnv tyname = tyname -> Kind

extKindEnv :: Kind -> KindEnv tyname -> KindEnv (S tyname)
extKindEnv k kindOf FZ     = k
extKindEnv k kindOf (FS i) = kindOf i

checkKind :: Kind -> Type tyname -> Reader (KindEnv tyname) Cool
checkKind Star        TyVoid          = pure true
checkKind Star        (a :-> b)       = (&&&) <$> checkKind Star a <*> checkKind Star b
checkKind Star        (TyForall k a)  = withReader (extKindEnv k) (checkKind Star a)
checkKind k           (TyVar i)       = do kindOf <- ask; pure (toCool (k == kindOf i))
checkKind (k :=> k')  (TyLam a)       = withReader (extKindEnv k) (checkKind k' a)
checkKind k'          (TyApp a b k)   = (&&&) <$> checkKind (k :=> k') a <*> checkKind k' b
checkKind _           _               = pure false
\end{code}


\subsection{Type Normalisation}

\begin{code}
type TySub tyname tyname' = tyname -> Type tyname'

extTySub :: TySub tyname tyname' -> TySub (S tyname) (S tyname')
extTySub s FZ      = TyVar FZ
extTySub s (FS i)  = FS <$> s i

appTySub :: TySub tyname tyname' -> Type tyname -> Type tyname'
appTySub s TyVoid          = TyVoid
appTySub s (a :-> b)       = appTySub s a :-> appTySub s b
appTySub s (TyForall k a)  = TyForall k (appTySub (extTySub s) a)
appTySub s (TyVar i)       = s i
appTySub s (TyLam a)       = TyLam (appTySub (extTySub s) a)
appTySub s (TyApp a b k)   = TyApp (appTySub s a) (appTySub s b) k

stepTy :: Type tyname -> Maybe (Type tyname)
stepTy TyVoid                 =    empty
stepTy (a :-> b)              =    ((:->) <$> stepTy a <*> pure b)
                              <|>  ((:->) <$> pure a <*> stepTy b)
stepTy (TyForall k a)         =    TyForall <$> pure k <*> stepTy a
stepTy (TyLam a)              =    TyLam <$> stepTy a
stepTy (TyVar i)              =    empty
stepTy (TyApp (TyLam a) b k)  =    pure (appTySub (\case FZ -> b; FS i -> TyVar i) a)
stepTy (TyApp a b k)          =    (TyApp <$> stepTy a <*> pure b <*> pure k)
                              <|>  (TyApp <$> pure a <*> stepTy b <*> pure k)

normaliseTy :: Type tyname -> Type tyname
normaliseTy a = maybe a normaliseTy (stepTy a)
\end{code}


\subsection{Terms}

\begin{code}
data Term tyname name
  = Var name
  | Lam (Term tyname (S name))
  | App (Term tyname name) (Term tyname name) (Normal (Type tyname))
  | LAM (Term (S tyname) name)
  | APP (Term tyname name) (Normal (Type (S tyname))) (Normal (Type tyname)) Kind
  deriving (Typeable, Eq, Show)

deriveBifunctor   ''Term
deriveEnumerable  ''Term
\end{code}


\subsection{Type Checking}

\begin{code}
type TyEnv tyname name = name -> Type tyname

extTyEnv :: Type tyname -> TyEnv tyname name -> TyEnv tyname (S name)
extTyEnv a typeOf  FZ      = a
extTyEnv a typeOf  (FS n)  = typeOf n

raiseTyEnv :: TyEnv tyname name -> TyEnv (S tyname) name
raiseTyEnv typeOf n = FS <$> typeOf n

checkType :: Eq tyname => Type tyname -> Term tyname name -> Reader (KindEnv tyname, TyEnv tyname name) Cool
checkType a               (Var n)                          =    do (kindOf, typeOf) <- ask; pure (toCool (a == typeOf n))
checkType (a :-> b)       (Lam x)                          =    withReader (bimap id (extTyEnv a)) (checkType b x)
checkType b               (App x y (Normal a))             =    (&&&) <$> checkType (a :-> b) x <*> checkType a y
checkType (TyForall k a)  (LAM x)                          =    withReader (bimap (extKindEnv k) raiseTyEnv) (checkType a x)
checkType c               (APP x (Normal a) (Normal b) k)  =    (\b1 b2 b3 -> b1 &&& b2 &&& b3)
                                                           <$>  checkType (TyForall k a) x
                                                           <*>  withReader fst (checkKind k b)
                                                           <*>  pure (c == normaliseTy (TyApp (TyLam a) b k))
checkType _               _                                =    pure false
\end{code}

\begin{code}
check :: Type Z -> Term Z Z -> Cool
check a x = runReader (checkType a x) (fromZ, fromZ)
\end{code}


\subsubsection{Enumerating System F\textomega}

\begin{code}
polygen :: Int -> Type Z -> IO [Term Z Z]
polygen depth a = search depth (check a)

main :: IO ()
main = do
  args <- getArgs
  case (length args, read (args !! 0), read (args !! 1)) of
    (2, d, a) -> mapM_ print =<< polygen d a
    (_, _, _) -> putStrLn "usage: polygen [depth] [type]"
\end{code}
