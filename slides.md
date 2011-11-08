% Pascal Wittmann
% Security of Multithreaded Programms by Compilation
% December 1-2, 2011

# Overview
  - Why formal methods?
  - Security problems of multithreaded programs.
  - Discussion of a solution.
  - Other/related solutions.
  - Conclusion / Outlook.

# Why formal methods?

# Security problems of multithreaded programs
  - There are private (_high_) and public (_low_) variables
  - The attacker has access to low-level variables
  - Sequential:
    - explicit flows: `lo := hi`
    - implicit flows: `if hi then lo := 1`
  - Concurrent:
    - internal timing leak: \newline `if hi {sleep(100)}; lo := 1 || sleep(50); lo := 0`
    - other example: `hi := 0; lo = x || hi := private-data`
  - I don't cover external timing leaks

# Discussion of a solution
  - Syntax & Semantic of multithreaded programs3
    - Program
    - State & Security environment
    - Scheduler
  - Typ system & it's soundness
  - Concrete instantiation
  - Type preserving compilation

# Program
We have a set of sequential Instructions $SeqIns$ and a primitive
\texttt{start} _pc_ that spawns a new thread.

\begin{definition}[Program P]
  \begin{enumerate}
  \item A set of program points P, with a distinguised entry point 1 and exit point \texttt{exit}
  \item A map from $P$ to $Ins$, where $Ins = SeqIns \cup \{start pc\}$ and $pc \in P \setminus \{\mathtt{stop}\}$.
        This map is refered to as P[i].
  \end{enumerate}
\end{definition}

Further, a relation $\mapsto \subseteq P \times P$ that describes possible successor instructions
and it's reflexsiv and transitive closure $\mapsto^*$.

# State
We have a set of local states, \texttt{LocState} and a global memory \texttt{GMemory}.
In Addition we have a set of thread identifiers \texttt{Thread}.

\begin{definition}[State]
  \begin{enumerate}
  \item \texttt{SeqState} is a product \texttt{LocState} $\times$ \texttt{GMemory}
  \item \texttt{ConcState} is a product (\texttt{Thread} $\rightharpoonup$ \texttt{LocState}) $\times$ \texttt{GMemory}
  \end{enumerate}
\end{definition}

Accessors for a state $s$:

  - s.lst and s.gmem are projections on the first and second component
  - s.act is the set of active threads
  - s.pc(tid) retrieves the current program point of the thread tid

# Security environment
We assume a set of levels \texttt{Level} = \{_low_, _high_\} where _low_ < _high_
with an attacker on level _low_.

\begin{definition}[Security environment]
   \begin{enumerate}
   \item A function $se : P \rightarrow \mathtt{Level}$
   \item A program point $i \in P$ is:
     \begin{itemize}
     \item low if $se(i) = low$, written $L(i)$
     \item high if $se(i) = high$, written $H(i)$
     \item always high if $\forall j \in P . i \mapsto^* j \rightarrow se(j) = high$, written $AH(i)$
     \end{itemize}
   \end{enumerate}
\end{definition}

Now we classify threads in:
\begin{align*}
s.lowT &= \{tid \in s.act | L(s.pc(tid))\} \\
s.highT &= \{tid \in s.act | H(s.pc(tid))\} \\
s.ahighT &= \{tid \in s.act | AH(s.pc(tid))\} \\
s.hidT &= \{tid \in s.act | H(s.pc(tid)) \land \lnot AH(s.pc(tid))\} 
\end{align*}

# History & Scheduler

\begin{definition}[History]
A History \texttt{History} is a list of pairs $(tid, l)$, where tid $\in$ \texttt{Thread}
and $l \in$ \texttt{Level}.
\end{definition}

\begin{definition}[Scheduler]
A scheduler is a function $pickt : ConcState \times History \rightharpoonup Thread$
that statisfies these conditions:
   \begin{enumerate}
   \item Always picks active threads
   \item if s.hidT $\neq \emptyset$ then pick(s, h) $\in$ s.hightT
   \item Only uses low names and the low part of the history to pick a low thread
   \end{enumerate}
\end{definition}

# Type system & Soundness
\texttt{LType} is a poset of local types.

\begin{definition}[Typable program]
A program is typable if
  \begin{enumerate}
  \item for all initial program points holds $S(i) = t_{init}$ and
  \item $\forall i, j \in P: (i \mapsto j) \rightarrow \exists s \in \mathtt{LType} \ . \ se, i \vdash S(i) \Rightarrow s \land S(j) \leq s$
  \end{enumerate}
where $S : P \rightarrow \mathtt{LType}$ and a security environment $se$.
\end{definition}

# Other/related solutions
  - Volpano & Smith use a \texttt{protect(c)} method
  - Russo & Sabelfeld use \texttt{hide} and \texttt{unhide} primitives.
  - Disallowing races on public data
  - …

# Conclusion / Outlook
