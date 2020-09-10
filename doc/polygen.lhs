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
{-# LANGUAGE PatternSynonyms      #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}
\end{code}
\end{comment}

\begin{comment}
\begin{code}
module PolyGen where
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
\end{code}
\end{comment}


\subsection{Terms}

\begin{code}
data Z
\end{code}
\begin{comment}
\begin{code}
  deriving (Typeable, Eq, Read, Show)
\end{code}
\end{comment}

\begin{code}
data S n = FZ | FS n
\end{code}
\begin{comment}
\begin{code}
  deriving (Typeable, Eq, Read, Functor)
\end{code}
\end{comment}

\begin{code}
fromZ :: Z -> a
fromZ n = case n of {}
\end{code}

\begin{code}
fromS :: a -> (n -> a) -> S n -> a
fromS z s FZ      = z
fromS z s (FS n)  = s n
\end{code}

\begin{comment}
\begin{code}
instance Enumerable Z where
  enumerate = datatype []

instance Enumerable n => Enumerable (S n) where
  enumerate = share $ aconcat [c0 FZ, c1 FS]
\end{code}
\end{comment}

\begin{comment}
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
\end{comment}


\subsection{Kinds}

\begin{code}
data  Kind
   =  Star
   |  Kind :=> Kind
\end{code}
\begin{comment}
\begin{code}
  deriving (Typeable, Eq, Read, Show)
\end{code}
\end{comment}

\begin{comment}
\begin{code}
deriveEnumerable ''Kind
\end{code}
\end{comment}


\subsection{Types}

\begin{code}
data  Type ty
   =  TyVoid
   |  Type ty :-> Type ty
   |  TyForall Kind (Type (S ty))
   |  TyVar ty
   |  TyLam (Type (S ty))
   |  TyApp (Type ty) (Type ty) Kind
\end{code}
\begin{comment}
\begin{code}
  deriving (Typeable, Eq, Read, Show, Functor)
\end{code}
\end{comment}

\begin{comment}
\begin{code}
deriveEnumerable ''Type
\end{code}
\end{comment}


\begin{code}
newtype Normal a = Normal { unNormal :: a }
\end{code}
\begin{comment}
\begin{code}
  deriving (Typeable, Eq, Functor)

instance Show a => Show (Normal a) where
  showsPrec d a = showsPrec d (unNormal a)
\end{code}
\end{comment}

\begin{comment}
\begin{code}
instance Enumerable ty => Enumerable (Normal (Type ty)) where
  enumerate = share $ aconcat
    [        c1  $ \a  ->  Normal (unNeutral a)
    , pay .  c1  $ \a  ->  Normal (TyLam (unNormal a))
    ]
\end{code}
\end{comment}


\begin{code}
newtype Neutral a = Neutral { unNeutral :: a }
\end{code}
\begin{comment}
\begin{code}
  deriving (Typeable, Eq, Functor)

instance Show a => Show (Neutral a) where
  showsPrec d a = showsPrec d (unNeutral a)
\end{code}
\end{comment}


\begin{comment}
\begin{code}
instance Enumerable ty => Enumerable (Neutral (Type ty)) where
  enumerate = share $ aconcat
    [  pay .  c0  $             Neutral TyVoid
    ,  pay .  c2  $ \a b    ->  Neutral (unNeutral a :-> unNeutral b)
    ,  pay .  c2  $ \k a    ->  Neutral (TyForall k (unNeutral a))
    ,  pay .  c1  $ \i      ->  Neutral (TyVar i)
    ,  pay .  c3  $ \a b k  ->  Neutral (TyApp (unNeutral a) (unNormal b) k)
    ]
\end{code}
\end{comment}


\subsection{Kind Checking}

\begin{code}
type KindEnv ty = ty -> Kind
\end{code}

\begin{code}
extKindEnv :: Kind -> KindEnv ty -> KindEnv (S ty)
extKindEnv k kindOf FZ     = k
extKindEnv k kindOf (FS i) = kindOf i
\end{code}

\begin{code}
checkTy :: Kind -> Type ty -> Reader (KindEnv ty) Cool
checkTy Star TyVoid = return true
checkTy Star (a :-> b) = do
  aOk <- checkTy Star a
  bOk <- checkTy Star b
  return (aOk &&& bOk)
checkTy Star (TyForall k a) =
  withReader (extKindEnv k) (checkTy Star a)
checkTy k (TyVar i) = do
  kindOf <- ask
  return (toCool (k == kindOf i))
checkTy (k :=> k') (TyLam a) =
  withReader (extKindEnv k) $
    checkTy k' a
checkTy k' (TyApp a b k) = do
  aOk <- checkTy (k :=> k') a
  bOk <- checkTy k' b
  return (aOk &&& bOk)
checkTy _ _ = return false
\end{code}


\subsection{Type Normalisation}

\begin{code}
type TySub ty ty' = ty -> Type ty'
\end{code}

\begin{code}
extTySub :: TySub ty ty' -> TySub (S ty) (S ty')
extTySub s FZ      = TyVar FZ
extTySub s (FS i)  = FS <$> s i
\end{code}

\begin{code}
appTySub :: TySub ty ty' -> Type ty -> Type ty'
appTySub s TyVoid          = TyVoid
appTySub s (a :-> b)       = appTySub s a :-> appTySub s b
appTySub s (TyForall k a)  = TyForall k (appTySub (extTySub s) a)
appTySub s (TyVar i)       = s i
appTySub s (TyLam a)       = TyLam (appTySub (extTySub s) a)
appTySub s (TyApp a b k)   = TyApp (appTySub s a) (appTySub s b) k
\end{code}

\begin{code}
pattern TyRed a b k = TyApp (TyLam a) b k
\end{code}

\begin{code}
stepTy :: Type ty -> Maybe (Type ty)
stepTy TyVoid                 = empty
stepTy (a :-> b)              =
  ((:->) <$> stepTy a <*> pure b) <|>
  ((:->) <$> pure a <*> stepTy b)
stepTy (TyForall k a)         = TyForall <$> pure k <*> stepTy a
stepTy (TyLam a)              = TyLam <$> stepTy a
stepTy (TyVar i)              = empty
stepTy (TyRed a b k)          = pure (appTySub (fromS b TyVar) a)
stepTy (TyApp a b k)          =
  (TyApp <$> stepTy a <*> pure b <*> pure k) <|>
  (TyApp <$> pure a <*> stepTy b <*> pure k)
\end{code}

\begin{code}
normTy :: Type ty -> Type ty
normTy a = maybe a normTy (stepTy a)
\end{code}


\subsection{Terms}

\begin{code}
data  Term ty tm
   =  Var  tm
   |  Lam  (Term ty (S tm))
   |  App  (Term ty tm)
           (Term ty tm)
           (Normal (Type ty))
   |  LAM  (Term (S ty) tm)
   |  APP  (Term ty tm)
           (Normal (Type (S ty)))
           (Normal (Type ty))
           Kind
\end{code}
\begin{comment}
\begin{code}
   deriving (Typeable, Eq, Show)

deriveBifunctor   ''Term
deriveEnumerable  ''Term
\end{code}
\end{comment}


\subsection{Type Checking}

\begin{code}
type TyEnv ty tm = tm -> Type ty
\end{code}

\begin{code}
extTyEnv :: Type ty -> TyEnv ty tm -> TyEnv ty (S tm)
extTyEnv a typeOf  FZ      = a
extTyEnv a typeOf  (FS n)  = typeOf n
\end{code}

\begin{code}
raiseTyEnv :: TyEnv ty tm -> TyEnv (S ty) tm
raiseTyEnv typeOf n = FS <$> typeOf n
\end{code}

\begin{code}
checkTm ::  Eq ty => Type ty -> Term ty tm ->
            Reader (KindEnv ty, TyEnv ty tm) Cool
checkTm a (Var n) = do
  (kindOf, typeOf) <- ask
  return (toCool (a == typeOf n))
checkTm (a :-> b) (Lam x) =
  withReader (bimap id (extTyEnv a)) $
    checkTm b x
checkTm b (App x y (Normal a)) = do
  xOk <- checkTm (a :-> b) x
  yOk <- checkTm a y
  return (xOk &&& yOk)
checkTm (TyForall k a) (LAM x) =
  withReader (bimap (extKindEnv k) raiseTyEnv) $
    checkTm a x
checkTm c (APP x (Normal a) (Normal b) k) = do
  xOk <- checkTm (TyForall k a) x
  yOk <- withReader fst (checkTy k b)
  return (xOk &&& yOk &&& c == normTy (TyRed a b k))
checkTm _ _ = return false
\end{code}

\begin{code}
checkClosedTm :: Type Z -> Term Z Z -> Cool
checkClosedTm a x =
  runReader (checkTm a x) (fromZ, fromZ)
\end{code}


\subsubsection{Enumerating System F\textomega}

\begin{code}
polygen :: Int -> Type Z -> IO [Term Z Z]
polygen depth a = search depth (checkClosedTm a)
\end{code}
