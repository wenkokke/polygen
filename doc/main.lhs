%% For double-blind review submission, w/o CCS and ACM Reference (max submission space)
\documentclass[sigplan,10pt,review,anonymous]{acmart}\settopmatter{printfolios=true,printccs=false,printacmref=false}

%% Conference information
\acmConference[PLDI'21]{ACM SIGPLAN Conference on Programming Language Design and Implementation}{June 20--25, 2021}{Virtual Conference}
\acmYear{2018}
\acmISBN{}
\acmDOI{}
\startPage{1}

%% Copyright information
\setcopyright{none}
%\setcopyright{acmcopyright}
%\setcopyright{acmlicensed}
%\setcopyright{rightsretained}

%% Bibliography style
\bibliographystyle{ACM-Reference-Format}
\citestyle{acmauthoryear}  %% For author/year citations

%% Preamble.
\usepackage{comment}
\usepackage{textgreek}
\let\Bbbk\undefined
%include lhs2TeX.fmt

\begin{document}

\title{PolyGen}

\author{Wen Kokke}
\affiliation{
  \institution{University of Edinburgh}
  \country{United Kingdom}
}
\email{wen.kokke@@ed.ac.uk}

%% TODO: Add yourself...


%% Abstract
\begin{abstract}
Text of abstract \ldots.
\end{abstract}


%% 2012 ACM Computing Classification System (CSS) concepts
%% Generate at 'http://dl.acm.org/ccs/ccs.cfm'.
\begin{CCSXML}
<ccs2012>
<concept>
<concept_id>10011007.10011006.10011008</concept_id>
<concept_desc>Software and its engineering~General programming languages</concept_desc>
<concept_significance>500</concept_significance>
</concept>
<concept>
<concept_id>10003456.10003457.10003521.10003525</concept_id>
<concept_desc>Social and professional topics~History of programming languages</concept_desc>
<concept_significance>300</concept_significance>
</concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Software and its engineering~General programming languages}
\ccsdesc[300]{Social and professional topics~History of programming languages}
%% End of generated code


%% Keywords
%% comma separated list
\keywords{keyword1, keyword2, keyword3}  %% \keywords are mandatory in final camera-ready submission

%% \maketitle
%% Note: \maketitle command must come after title commands, author
%% commands, abstract environment, Computing Classification System
%% environment and commands, and keywords command.
\maketitle

\section{PolyGen}

%include src/polygen.lhs

%% Bibliography
\bibliography{main}

%% Appendix
\appendix
\section{Appendix}

Text of appendix \ldots

\end{document}
