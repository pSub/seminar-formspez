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
    - explicit flows: `public := private`
    - implicit flows: `if private then public := 1`
  - Concurrent:
    - internal timing leak: \newline `if private {sleep(100)}; public := 1 || sleep(50); public := 0`

# Discussion of a solution
  - Syntax & Semantic of multithreaded programs
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

# Other/related solutions

# Conclusion / Outlook
