\section{PolyGen}

\todo{Describe NEAT and the |Enumerable| typeclass.}

\todo{Describe behaviour of the derived instances of |Enumerable|.}

\todo{Describe why intrinsically-typed enumerators can't be efficient.}

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
{-# LANGUAGE StandaloneDeriving   #-}
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
import Control.Monad.Reader (Reader, ask, runReader, withReader)
import Data.Bifunctor
import Data.Bifunctor.TH
import Data.Coolean
import Data.Maybe
import Data.Proxy
import Test.Feat.Access (valuesWith)
\end{code}
\end{comment}


\subsection{Variables and DeBruijn Indices}

We use \emph{finite types} to represent well-scoped deBruijn indices. Finite types are natural numbers, indexed on the type-level by an upper bound. While they are often implemented as GADTs, we can approximate finite types in Haskell98 using two datatypes~\cite[following][FEAT examples]{duregaard2016}:
\begin{code}
data Z                -- Z has 0 inhabitants
data S n = FZ | FS n  -- S n has n + 1 inhabitants
\end{code}
For instance, the type |S (S Z)| is the type of natural numbers smaller than two, and so has two elements: |FZ| and |FS FZ|.

We derive instances for |Eq|, |Functor| (for |S|), |Show| (via |Int| for readability), among others, for finite types, and define the eliminators |fromZ| and |fromS|:
\begin{comment}
\begin{code}
deriving instance Eq Z
deriving instance Read Z
deriving instance Show Z
deriving instance Typeable Z
deriving instance Eq n => Eq (S n)
deriving instance Functor S
deriving instance Read n => Read (S n)
deriving instance Typeable n => Typeable (S n)
-- Deriving Show via Int:
class Enumerable n =>  Fin n       where toInt  :: n -> Int
instance               Fin Z       where toInt  = fromZ
instance Fin n =>      Fin (S n)   where toInt  = fromS 0 (succ . toInt)
instance Fin (S n) =>  Show (S n)  where show   = show . toInt
\end{code}
\end{comment}
\begin{code}
fromZ :: Z -> a
fromZ n = case n of {} -- No inhabitants, no cases.

fromS :: a -> (n -> a) -> (S n -> a)
fromS fz fs FZ      = fz
fromS fz fs (FS n)  = fs n
\end{code}
The eliminators serve an important role: if we view type environments as functions from names to types, then |fromZ| is the empty environment, and |fromS| extends the environment with a new type.

The number of inhabitants of a finite type is finite, so we don't need to use a size-based enumeration. Instead, we declare a custom instance of |Enumerable|, which enumerates all inhabitants of a finite type at size 0:
\begin{code}
instance Enumerable Z where
  enumerate = share . aconcat $ []

instance Enumerable n => Enumerable (S n) where
  enumerate = share . aconcat $ [c0 FZ, c1 FS]
\end{code}
\begin{comment}
\begin{code}
enumFin :: Fin n => [n]
enumFin = concat (snd <$> valuesWith global)
\end{code}
\end{comment}
Enumerating all values of type |S (S (S Z))| returns \eval{enumFin @(S (S (S Z)))}.

\subsection{Kinds and Types}

\subsubsection{Syntax}

\begin{code}
infixr 7 :=> :->

data  Kind
   =  Star
   |  Kind :=> Kind
\end{code}

\begin{comment}
\begin{code}
deriving instance Eq Kind
deriving instance Read Kind
deriving instance Show Kind
deriving instance Typeable Kind
deriveEnumerable ''Kind
\end{code}
\end{comment}

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
deriving instance Eq ty => Eq (Type ty)
deriving instance Functor Type
deriving instance Read ty => Read (Type ty)
deriving instance (Show ty, Fin ty) => Show (Type ty)
deriving instance Typeable ty => Typeable (Type ty)
deriveEnumerable ''Type
\end{code}
\end{comment}

\medskip

\begin{code}
newtype Normal   a = Normal   { unNormal   :: a }
newtype Neutral  a = Neutral  { unNeutral  :: a }
\end{code}

\begin{code}
instance  Enumerable ty =>
          Enumerable (Normal (Type ty)) where
  enumerate = share . aconcat $
    [        c1  $ \(Neutral  a) -> Normal a
    , pay .  c1  $ \(Normal   a) -> Normal (TyLam a)
    ]

instance  Enumerable ty =>
          Enumerable (Neutral (Type ty)) where
  enumerate = share . aconcat . fmap pay $
    [  c0  $                                   Neutral TyVoid
    ,  c2  $ \(Neutral a)  (Neutral  b)    ->  Neutral (a :-> b)
    ,  c2  $ \k            (Neutral  a)    ->  Neutral (TyForall k a)
    ,  c1  $ \i                            ->  Neutral (TyVar i)
    ,  c3  $ \(Neutral a)  (Normal   b) k  ->  Neutral (TyApp a b k)
    ]
\end{code}

\begin{comment}
\begin{code}
deriving instance Eq a => Eq (Neutral a)
deriving instance Functor Neutral
deriving instance Typeable a => Typeable (Neutral a)

instance Show a => Show (Neutral a) where
  showsPrec d a = showsPrec d (unNeutral a)

deriving instance Eq a => Eq (Normal a)
deriving instance Functor Normal
deriving instance Typeable a => Typeable (Normal a)

instance Show a => Show (Normal a) where
  showsPrec d a = showsPrec d (unNormal a)
\end{code}
\end{comment}

\begin{comment}
\begin{code}
enumNeutralTy :: Enumerable ty => Int -> [Neutral (Type ty)]
enumNeutralTy depth = concat (snd <$> take depth (valuesWith global))
\end{code}
\end{comment}


\subsubsection{Kind Checking}

\begin{code}
type KindEnv ty = ty -> Kind
\end{code}

\medskip

\begin{code}
extKindEnv :: Kind -> KindEnv ty -> KindEnv (S ty)
extKindEnv k kindOf = fromS k kindOf
\end{code}

\medskip

\begin{code}
checkTy :: Kind -> Type ty -> Reader (KindEnv ty) Cool
checkTy Star TyVoid = return true
checkTy Star (a :-> b) = do
  aOk <- checkTy Star a
  bOk <- checkTy Star b
  return (aOk &&& bOk)
checkTy Star (TyForall k a) =
  withReader (extKindEnv k) $ checkTy Star a
checkTy k (TyVar i) = do
  kindOf <- ask
  return (toCool (k == kindOf i))
checkTy (k :=> k') (TyLam a) =
  withReader (extKindEnv k) $ checkTy k' a
checkTy k' (TyApp a b k) = do
  aOk <- checkTy (k :=> k') a
  bOk <- checkTy k' b
  return (aOk &&& bOk)
checkTy _ _ = return false
\end{code}


\subsubsection{Type Normalisation}

\begin{code}
type TySub ty ty' = ty -> Type ty'
\end{code}

\medskip

\begin{code}
extTySub :: TySub ty ty' -> TySub (S ty) (S ty')
extTySub s = fromS (TyVar FZ) (fmap FS . s)
\end{code}

\medskip

\begin{code}
appTySub :: TySub ty ty' -> Type ty -> Type ty'
appTySub s TyVoid          = TyVoid
appTySub s (a :-> b)       = appTySub s a :-> appTySub s b
appTySub s (TyForall k a)  = TyForall k (appTySub (extTySub s) a)
appTySub s (TyVar i)       = s i
appTySub s (TyLam a)       = TyLam (appTySub (extTySub s) a)
appTySub s (TyApp a b k)   = TyApp (appTySub s a) (appTySub s b) k
\end{code}

\medskip

\begin{code}
pattern TyRed a b k = TyApp (TyLam a) b k
\end{code}

\medskip

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

\medskip

\begin{code}
normTy :: Type ty -> Type ty
normTy a = maybe a normTy (stepTy a)
\end{code}


\subsection{Terms}

\subsubsection{Syntax}

\begin{code}
data  Term ty tm
   =  Var  tm                      -- deBruijn index
   |  Lam  (Term ty (S tm))        -- \lambda-abstraction body
   |  App  (Term ty tm)            -- function
           (Term ty tm)            -- argument
           (Normal (Type ty))      -- argument type
   |  LAM  (Term (S ty) tm)        -- \Lambda-abstraction body
   |  APP  (Term ty tm)            -- polymorphic term
           (Normal (Type (S ty)))  -- codomain of \forall
           (Normal (Type ty))      -- concrete type
           Kind                    -- concrete type kind
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

\medskip

\begin{code}
extTyEnv :: Type ty -> TyEnv ty tm -> TyEnv ty (S tm)
extTyEnv a typeOf = fromS a typeOf
\end{code}

\medskip

\begin{code}
raiseTyEnv :: TyEnv ty tm -> TyEnv (S ty) tm
raiseTyEnv typeOf n = FS <$> typeOf n
\end{code}

\medskip

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
  bOk <- withReader fst (checkTy k b)
  let cOk = normTy (TyRed a b k) == c
  return (xOk &&& bOk &&& cOk)
checkTm _ _ = return false
\end{code}

\medskip

\begin{code}
checkClosedTm :: Type Z -> Term Z Z -> Cool
checkClosedTm a x =
  runReader (checkTm a x) (fromZ, fromZ)
\end{code}


\subsection{Enumerating System F\textomega}

\begin{code}
enumClosedTm :: Int -> Type Z -> IO [Term Z Z]
enumClosedTm depth a = search depth (checkClosedTm a)
\end{code}
