\documentclass[acmsmall]{acmart}

% workaround for duplicate symbols:
\let\oldBbbk\Bbbk%
\let\Bbbk\undefined%

% lhs2TeX:
%include polycode.fmt

%%
%% \BibTeX command to typeset BibTeX logo in the docs
\AtBeginDocument{%
  \providecommand\BibTeX{{%
    Bib\TeX}}}

%% Rights management information.  This information is sent to you
%% when you complete the rights form.  These commands have SAMPLE
%% values in them; it is your responsibility as an author to replace
%% the commands and values with those provided to you when you
%% complete the rights form.
\setcopyright{acmlicensed}
\copyrightyear{2018}
\acmYear{2018}
\acmDOI{XXXXXXX.XXXXXXX}

%%
%% These commands are for a JOURNAL article.
\acmJournal{JACM}
\acmVolume{37}
\acmNumber{4}
\acmArticle{111}
\acmMonth{8}

%%
%% Submission ID.
%% Use this when submitting an article to a sponsored event. You'll
%% receive a unique submission ID from the organizers
%% of the event, and this ID should be used as the parameter to this command.
%%\acmSubmissionID{123-A56-BU3}

%%
%% For managing citations, it is recommended to use bibliography
%% files in BibTeX format.
%%
%% You can then either use BibTeX with the ACM-Reference-Format style,
%% or BibLaTeX with the acmnumeric or acmauthoryear sytles, that include
%% support for advanced citation of software artefact from the
%% biblatex-software package, also separately available on CTAN.
%%
%% Look at the sample-*-biblatex.tex files for templates showcasing
%% the biblatex styles.
%%

%%
%% The majority of ACM publications use numbered citations and
%% references.  The command \citestyle{authoryear} switches to the
%% "author year" style.
%%
%% If you are preparing content for an event
%% sponsored by ACM SIGGRAPH, you must use the "author year" style of
%% citations and references.
%% Uncommenting
%% the next command will enable that style.
\citestyle{acmauthoryear}

% Preamble:
%format |>           = "\triangleright"
%format :>           = "\mathbin{{:}\triangleright}"

%format α            = "\alpha"
%format α_α          = "\alpha\_\alpha"
%format β            = "\beta"
%format γ            = "\gamma"
%format δ            = "\delta"
%format ε            = "\epsilon"
%format κ            = "\kappa"
%format κ'           = "\kappa^{\prime}"
%format ρ            = "\rho"
%format ρ'           = "\rho^{\prime}"
%format ρ''          = "\rho^{\prime\prime}"
%format σ            = "\sigma"
%format τ            = "\tau"
%format τ'           = "\tau^{\prime}"
%format τ''          = "\tau^{\prime\prime}"
%format ω            = "\omega"
%format ★            = "\star"

%format forall       = "\mathbf{forall}"

%format (MkNorm (a)) = a
%format (MkNeut (a)) = a

%format :=>          = "\mathbin{{:}\mkern-5mu\Rightarrow}"
%format :->          = "\mathbin{{:}\mkern-5mu\rightarrow}"
%format !&&          = "\landseq"
%format !!&&         = "\landseq"
%format &&&          = "\land"
%format |||          = "\lor"
%format <|>          = "\mathbin{\langle\mid\rangle}"
%format <*>          = "\mathbin{\langle\star\rangle}"
%format <$>          = "\mathbin{\langle\$\rangle}"
%format <>           = "\mathbin{\diamond}"

%format checkTy      = "\Varid{check}_{\Varid{Ty}}"
%format checkTm      = "\Varid{check}_{\Varid{Tm}}"

%subst comment a     = "{\quad\color{hsann}\text{\textemdash}\ " a "}"
% Utility packages.
\usepackage{xspace}%

% Support Unicode characters.
%% \usepackage[T1]{fontenc} %% for diacritics: the default is 'OT1'
\usepackage[utf8]{inputenc} %% pdflatex: For UTF-8 input support.
\usepackage{newunicodechar} %% Map Unicode characters to LaTeX commands.

% Packages with various characters.
\usepackage{textgreek}

% Unicode character mapping.
\newunicodechar{α}{{\textalpha}}
\newunicodechar{β}{{\textbeta}}
\newunicodechar{λ}{{\textlambda}}
\newunicodechar{ω}{{\textomega}}
\newunicodechar{ρ}{{\textrho}}
\newunicodechar{τ}{{\texttau}}
\newunicodechar{★}{\star}
\newunicodechar{⇒}{\Rightarrow}

% User-defined commands.
\colorlet{hsann}{gray}%
\def\hsannname{gray}%
\def\hsannword{\textcolor{hsann}{\hsannname}\xspace}%
\def\oftype{\mathrel{::}}
\newcommand{\hsann}[1]{\begingroup\color{hsann}#1\endgroup}
\newcommand{\field}[1]{\hsann\begingroup#1\oftype\endgroup}%
\def\landseq{\rotatebox[origin=c]{-28}{!}\!\!\!\land}

% Math paragraphs.
\usepackage{mathpartir}

%%
%% end of the preamble, start of the body of the document source.
\begin{document}

%%
%% The "title" command has an optional parameter,
%% allowing the author to define a "short title" to be used in page headers.
% Document title
\title{Functional Pearl: Let\textquotesingle s List All Programs!}

%%
%% The "author" command and its associated commands are used to define
%% the authors and their affiliations.
%% Of note is the shared affiliation of the first two authors, and the
%% "authornote" and "authornotemark" commands
%% used to denote shared contribution to the research.
\author{Wen Kokke}
\email{me@@wen.works}
\affiliation{%
    \institution{Well-Typed}
      \city{Glasgow}
        \country{UK}
  }

%%
%% By default, the full list of authors will be used in the page
%% headers. Often, this list is too long, and will overlap
%% other information printed in the page headers. This command allows
%% the author to define a more concise list
%% of authors' names for this purpose.

%%
%% The abstract is a short summary of the work to be presented in the
%% article.
\begin{abstract}
  To be written last\ldots{}
\end{abstract}

%%
%% The code below is generated by the tool at http://dl.acm.org/ccs.cfm.
%% Please copy and paste the code instead of the example below.
%%
\begin{CCSXML}
<ccs2012>
 <concept>
  <concept_id>00000000.0000000.0000000</concept_id>
  <concept_desc>Do Not Use This Code, Generate the Correct Terms for Your Paper</concept_desc>
  <concept_significance>500</concept_significance>
 </concept>
 <concept>
  <concept_id>00000000.00000000.00000000</concept_id>
  <concept_desc>Do Not Use This Code, Generate the Correct Terms for Your Paper</concept_desc>
  <concept_significance>300</concept_significance>
 </concept>
 <concept>
  <concept_id>00000000.00000000.00000000</concept_id>
  <concept_desc>Do Not Use This Code, Generate the Correct Terms for Your Paper</concept_desc>
  <concept_significance>100</concept_significance>
 </concept>
 <concept>
  <concept_id>00000000.00000000.00000000</concept_id>
  <concept_desc>Do Not Use This Code, Generate the Correct Terms for Your Paper</concept_desc>
  <concept_significance>100</concept_significance>
 </concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Do Not Use This Code~Generate the Correct Terms for Your Paper}
\ccsdesc[300]{Do Not Use This Code~Generate the Correct Terms for Your Paper}
\ccsdesc{Do Not Use This Code~Generate the Correct Terms for Your Paper}
\ccsdesc[100]{Do Not Use This Code~Generate the Correct Terms for Your Paper}

%%
%% Keywords. The author(s) should pick words that accurately describe
%% the work being presented. Separate the keywords with commas.
% Mandatory.
\keywords{\textcolor{red}{TODO: Set keywords}}

\received{20 February 2007}
\received[revised]{12 March 2009}
\received[accepted]{5 June 2009}

%%
%% This command processes the author and affiliation and title
%% information and builds the first part of the formatted document.
\maketitle

\section{Introduction}\label{introduction}

Nearly a decade ago, I was developing the type theory for a small
linearly-typed programming language and hoped to test it using
QuickCheck \cite{ClaessenH2000} before committing to a mechanised proof.
I was quickly told that generating simply-typed or even untyped
λ-calculus terms is no small feat. Eventually, during a visit to Sweden,
Koen Claessen pointed me to Jonas Duregård's \texttt{lazy-search}
package \cite{Duregard2016:lazy-search}. I wrote a very simple type
checker for my programming language in Haskell, passed it to
\texttt{lazy-search}, and it just\ldots{} churned away, quickly
producing well-typed terms. Did you know there are 26,982,292
simply-typed λ-terms with 30 or fewer constructors? It takes my machine
about a minute to list them all. I never looked back.

My motivation for writing this paper is twofold.

\section{Simply-Typed Lambda
Calculus}\label{simply-typed-lambda-calculus}

\begin{code}
import Control.Enumerable
import Control.Search
import Data.Coolean
\end{code}

\begin{code}
data Z
data S n = FZ | FS n
\end{code}

\begin{code}
instance Enumerable Z where
  enumerate = share empty

instance Enumerable n => Enumerable (S n) where
  enumerate = share . aconcat $ [c0 FZ, c1 FS]
\end{code}

\begin{code}
data Ty
  =  TyIota                                                      -- \iota
  |  ({-"\field{\tau}"-} Ty) :-> ({-"\field{\tau^\prime}"-} Ty)  -- \tau\rightarrow\tau^\prime
\end{code}

\begin{code}
data Tm n
  =  Var  ({-"\field{x}"-} n)                                                            -- x
  |  Lam  ({-"\field{e}"-} Tm (S n))                                                     -- \lambda x.e
  |  App  ({-"\field{e}"-} Tm n)  ({-"\field{e^\prime}"-} Tm n) ({-"\field{\tau}"-} Ty)  -- e \; e^{\prime\tau}
\end{code}

\begin{code}
type Tys n = n -> Ty
\end{code}

\begin{code}
nil :: Z -> a
nil n = case n of {}
\end{code}

\begin{code}
(|>) :: (n -> a) -> a -> (S n -> a)
(fs |> fz) FZ      = fz
(fs |> fz) (FS n)  = fs n
\end{code}

\begin{code}
check :: Tys n -> Tm n -> Ty -> Cool
check γ  (Var x)       τ           =  toCool (γ x == τ)
check γ  (App e e' τ)  τ'          =  check γ e (τ :-> τ') &&& check γ e' τ
check γ  (Lam e)       (τ :-> τ')  =  check (γ |> τ) e τ'
check _  _             _           =  false
\end{code}

\begin{code}
enumTmZ :: Int -> Ty -> IO [Tm Z]
enumTmZ depth τ = search depth (\e -> check nil e τ)
\end{code}

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

\section{System Fω}\label{system-fux3c9}

\begin{code}
data Ki
  =  Star                                                            -- \star
  |  ({-"\field{\kappa}"-} Ki) :=> ({-"\field{\kappa^\prime}"-} Ki)  -- \kappa\Rightarrow\kappa^\prime
\end{code}

\begin{code}
data  Ty m
   =  ({-"\field{\rho}"-} Ty m) :-> ({-"\field{\rho^\prime}"-} Ty m)                                -- \rho\rightarrow\rho^\prime
   |  TyVar  ({-"\field{\alpha}"-} m)                                                               -- \alpha
   |  TyLam  ({-"\field{\rho}"-} Ty (S m))                                                          -- \lambda x.\rho
   |  TyApp  ({-"\field{\rho}"-} Ty m) ({-"\field{\rho^\prime}"-} Ty m) ({-"\field{\kappa}"-}  Ki)  -- \rho\;\rho^{\prime\kappa}
   |  TyAll  ({-"\field{\kappa}"-} Ki) ({-"\field{\rho}"-} Ty (S m))                                -- \forall \alpha^{\kappa}.\rho
\end{code}

\begin{code}
type Kis m = m -> Ki
\end{code}

\begin{code}
checkTy :: Kis m -> Ty m -> Ki -> Cool
checkTy δ  (TyVar α)       κ           = toCool (δ α == κ)
checkTy δ  (TyLam ρ)       (κ :=> κ')  = checkTy (δ |> κ) ρ κ'
checkTy δ  (TyApp ρ ρ' κ)  κ'          = checkTy δ ρ (κ :=> κ') &&& checkTy δ ρ' κ
checkTy δ  (ρ :-> ρ')      Star        = checkTy δ ρ Star &&& checkTy δ ρ' Star
checkTy δ  (TyAll κ ρ)     Star        = checkTy (δ |> κ) ρ Star
checkTy _  _               _           = false
\end{code}

\inlinehs%
\begin{mathpar}
\mbox{%

\begin{code}
newtype Norm  a =  {-"\Varid{MkNorm}\;"-}  MkNorm  a
\end{code}

}
and
\mbox{%

\begin{code}
newtype Neut  a =  {-"\Varid{MkNeut}\;"-}  MkNeut  a
\end{code}

}
\end{mathpar}
\plainhs%

\begin{code}
data Tm m n
  =  Var  ({-"\field{x}"-} n)                                                                                                              -- x
  |  Lam  ({-"\field{e}"-} Tm m (S n))                                                                                                     -- \lambda x.e
  |  App  ({-"\field{e}"-} Tm m n) ({-"\field{e^\prime}"-} Tm m n) ({-"\field{\tau}"-} Norm (Ty m))                                        -- e\;e^{\prime\tau}
  |  LAM  ({-"\field{e}"-} Tm (S m) n)                                                                                                     -- \Lambda \alpha.e
  |  APP  ({-"\field{e}"-} Tm m n) ({-"\field{\kappa}"-} Ki) ({-"\field{\tau}"-} Norm (Ty (S m))) ({-"\field{\tau^\prime}"-} Norm (Ty m))  -- e^{\forall \alpha^\kappa.\tau}\;\tau^\prime
\end{code}

\begin{code}
type TySub m m' = m -> Ty m'
\end{code}

\begin{code}
ε :: TySub m m
ε = TyVar
\end{code}

\begin{code}
weak :: (Functor f) => (m -> f n) -> (m -> f (S n))
weak σ = fmap FS . σ
\end{code}

\begin{code}
sub :: TySub m m' -> Ty m -> Ty m'
sub σ = \case
  TyVar α       -> σ α
  TyLam ρ       -> TyLam (sub (weak σ |> TyVar FZ) ρ)
  TyApp ρ ρ' κ  -> TyApp (sub σ ρ) (sub σ ρ') κ
  ρ :-> ρ'      -> sub σ ρ :-> sub σ ρ'
  TyAll κ ρ     -> TyAll κ (sub (weak σ |> TyVar FZ) ρ)
\end{code}

\begin{code}
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
\end{code}

\begin{spec}
norm :: Ty m -> Norm (Ty m)
norm ρ = maybe (MkNorm ρ) norm (step ρ)
\end{spec}

\begin{code}
type Tys m n = n -> Ty m
\end{code}

\begin{code}
checkTm :: (Eq m) => Kis m -> Tys m n -> Tm m n -> Ty m -> Cool
checkTm δ γ  (Var x)                           τ            =    toCool (γ x == τ)
checkTm δ γ  (Lam e)                           (τ :-> τ')   =    checkTm δ (γ |> τ) e τ'
checkTm δ γ  (App f e (MkNorm τ))              τ'           =    checkTy δ τ Star
                                                            !&&  checkTm δ γ f (τ :-> τ') &&&  checkTm δ γ e τ
checkTm δ γ  (LAM e)                           (TyAll κ τ)  =    checkTm (δ |> κ) (weak γ) e τ
checkTm δ γ  (APP e κ (MkNorm τ) (MkNorm τ'))  τ''          =    checkTy δ (TyAll κ τ) Star &&&  checkTy δ τ' κ
                                                            !&&  checkTm δ γ e (TyAll κ τ) &&&  norm (sub (ε |> τ') τ) == MkNorm τ''
checkTm _ _  _                                 _            =    false
\end{code}

\begin{code}
loop :: Tm Z Z
loop = APP (LAM (Lam (Var FZ))) Star (MkNorm α_α) (MkNorm ω)
 where
  α_α :: Ty (S Z)
  α_α = TyApp (TyVar FZ) (TyVar FZ) Star

  ω :: Ty Z
  ω = TyLam (TyApp (TyVar FZ) (TyVar FZ) Star)
\end{code}

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

\section{Dependent Lambda Calculus}\label{dependent-lambda-calculus}

Annotations in \hsannword.

\begin{code}
type Ty n = Tm n
\end{code}

\begin{code}
data Tm n
  =  Var   ({-"\field{x}"-} n)                                                                                                                -- x
  |  Lam   ({-"\field{e}"-} Tm (S n))                                                                                                         -- \lambda x.e
  |  App   ({-"\field{e}"-} Tm n) ({-"\field{e^\prime}"-} Tm n) ({-"\field{\tau}"-} Norm (Ty n)) ({-"\field{\tau^\prime}"-} Norm (Ty (S n)))  -- e^{\forall{x^\tau}.\tau^\prime}\;e^\prime
  |  Star                                                                                                                                     -- \star
  |  Pi    ({-"\field{\rho}"-} Ty n) ({-"\field{\rho^\prime}"-} Ty (S n)) ({-"\field{\tau}"-} Norm (Ty n))                                    -- \forall{x^\rho}.\rho^\prime
\end{code}

\begin{code}
type Sub n n' = n -> Tm n'
\end{code}

\begin{code}
ε :: Sub n n
ε = Var
\end{code}

\begin{code}
sub :: Sub n n' -> Tm n -> Tm n'
sub σ = \case
  Var   i          -> σ i
  Lam   e          -> Lam  (sub (weak σ |> Var FZ) e)
  App   e e' τ τ'  -> App  (sub σ e) (sub σ e') (sub σ <$> τ) (sub (weak σ |> Var FZ) <$> τ')
  Star             -> Star
  Pi    ρ ρ' τ     -> Pi   (sub σ ρ) (sub (weak σ |> Var FZ) ρ') (sub σ <$> τ)
\end{code}

\begin{code}
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
\end{code}

\begin{spec}
norm :: Tm n -> Norm (Tm n)
norm e = maybe (MkNorm e) norm (step e)
\end{spec}

\begin{code}
type Tys n = n -> Ty n
\end{code}

\begin{code}
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
\end{code}

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

\section{Simply-Typed Linear Lambda
Calculus}\label{simply-typed-linear-lambda-calculus}

\begin{code}
data Use = None | Once | Many
\end{code}

\begin{code}
instance Semigroup Use where
  None  <>  u     = u
  u     <>  None  = u
  Once  <>  Once  = Many
  Many  <>  u     = Many
  u     <>  Many  = Many
\end{code}

\begin{code}
instance Monoid Use where
  mempty = None
\end{code}

\begin{code}
data Uses n where
  Nil   ::                   Uses Z
  (:>)  :: Uses n -> Use ->  Uses (S n)
\end{code}

\begin{code}
instance Semigroup (Uses n) where
  Nil      <>  Nil      = Nil
  us :> u  <>  vs :> v  = (us <> vs) :> (u <> v)
\end{code}

\begin{code}
class MkUses n where
  never   :: Uses n
  once    :: n -> Uses n
\end{code}

\begin{code}
instance MkUses Z where
  once    = nil
  never   = Nil
\end{code}

\begin{code}
instance (MkUses n) => MkUses (S n) where
  never   = never :> None
  once    = \case{FZ -> never :> Once; FS i -> once i :> None}
\end{code}

\begin{code}
instance (MkUses n) => Monoid (Uses n) where
  mempty = never
\end{code}

\begin{code}
checkUse :: (MkUses n) => Tm n -> (Uses n, Cool)
checkUse = \case
  Var x -> (once x, true)
  Lam e | (us :> u, eOk) <- checkUse e -> (us, eOk &&& u == Once)
  App e e' _ -> (&&&) <$> checkUse e <*> checkUse e'
\end{code}

%%
%% The acknowledgments section is defined using the "acks" environment
%% (and NOT an unnumbered section). This ensures the proper
%% identification of the section in the article metadata, and the
%% consistent spelling of the heading.
% Optional. Acknowledgements.

%%
%% The next two lines define the bibliography style to be used, and
%% the bibliography file.
\bibliographystyle{ACM-Reference-Format}
\bibliography{bibliography.bib}

% TODO: Support appendices.

\end{document}
\endinput
%%
%% End of file `sample-acmsmall.tex'.
