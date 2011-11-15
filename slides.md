% Pascal Wittmann
% "Security of Multithreaded Programms by Compilation" \newline by Gilles Barthe, Tamara Rezk, Alejandro Russo and Andrei Sabelfeld
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
  - The attacker can observe low-level variables
  - Sequential:
    - explicit flows: `lo := hi`
    - implicit flows: `if hi then lo := 1`
  - Concurrent:
    - internal timing leak: \newline `if hi {sleep(100)}; lo := 1 || sleep(50); lo := 0`
    - other example: `hi := 0; lo = x || hi := private-data`
  - External timing leaks are not covered

# Discussion of a solution
  - Syntax & Semantic of multithreaded programs
    - Program
    - State & Security environment
    - Scheduler
  - Type system & it's soundness
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

# Type system
\texttt{LType} is a poset of local types.

Intuition of the type judgements: $se, i \vdash s \Rightarrow t$ means if executing
program point $i$ the type changes from $s$ to $t$ w.r.t a security environment $se$.

\begin{definition}[Typable program]
A program is typable if
  \begin{enumerate}
  \item for all initial program points holds $S(i) = t_{init}$ and
  \item $\forall i, j \in P: (i \mapsto j) \rightarrow \exists s \in \mathtt{LType} \ . \ se, i \vdash S(i) \Rightarrow s \land S(j) \leq s$
  \end{enumerate}
where $S : P \rightarrow \mathtt{LType}$ and a security environment $se$.
\end{definition}

# Soundness of the type system

# The next function

If the execution of program point $i$ results in a high thread, the
function $\mathtt{next}: P \rightharpoonup P$ calculates the program point in which the
thread becomes visible again.

The \texttt{next} function has to fulfill the following properties:
\begin{align}
&Dom(next) = \{i \in P | H(i) \land \neg AH(i)\} \\
&i, j \in Dom(next) \land i \mapsto j \Rightarrow next(i) = next(j) \\
&i \in Dom(next) \land j \not\in Dom(next) \land i \mapsto j \Rightarrow next(i) = j \\
&j, k \in Dom(next) \land i \not\in Dom(next) \land i \mapsto j \land i \mapsto k \land j \neq k \Rightarrow next(j) = next(k) \\
&i, j \in Dom(next) \land k \not\in Dom(next) \land i \mapsto j \land i \mapsto k \land j \neq k \Rightarrow next(j) = k \\
\end{align}

# Instantiation
  - Simple langugage with `if`, `;`, `:=`, `while` and `fork`
  - Assembly 
    - `push n` -- push value on the stack
    - `load x` -- push value of variable on the stack
    - `store x` -- store first element of the stack in x
    - `goto j` / `ifeq j` -- un-/conditional jump to j
    - `start j` -- create a new thread starting in j

# Transfer rules
\begin{prooftree}
\AxiomC{$P[i] = store x$}
\AxiomC{$se(i) \sqcup k \leq \Gamma(x)$}
\BinaryInfC{$se, i \vdash_{seq} k :: st \Rightarrow st$}
\end{prooftree}

\begin{prooftree}
\AxiomC{$P[i] = ifeq j$}
\AxiomC{$\forall j' \in reg(i), k \leq se(j')$}
\BinaryInfC{$se, i \vdash_{seq} k :: st \Rightarrow lift_k(st)$}
\end{prooftree}

where $reg : P \rightharpoonup P(P)$ computes the control dependence region and
$jun : P \rightharpoonup P$ computes the junction point.

Similar rules have to be established for the other commands of the target language.

# Concurrent extension


# sregion & tregion

# junction points & next function

# Adaption to the JVM
  - JVML's sequential type system is compatible with bytecode verifikation, thus it's compatible with the concurrent type system
  - The scheduler is mostly left unspecified, thus introducing a secure scheduler is possible
  - Issues
    - Method calls have a big-step semantic
    - This approach doesn't deal with synchronisation

# Other/related solutions
  - Volpano & Smith use a \texttt{protect(c)} method
  - Russo & Sabelfeld use \texttt{hide} and \texttt{unhide} primitives.
  - Disallowing races on public data
  - …

# Conclusion / Outlook
