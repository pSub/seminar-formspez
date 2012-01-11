% Security of Multithreaded Programms by Compilation
% Pascal Wittmann
% Seminar "Formal Specification" \newline December 1-2, 2011

### Outline
  - Why formal methods?
  - Security problems of multithreaded programs.
  - Discussion of a solution.
  - Other/related solutions.
  - Conclusion / Outlook.

####

# Introduction
## Why formal methods?
### Why formal methods?
  - Modeling precisely a part of the world
  - Formulate the problem unambiguous
  - Leaving unimportant things underspecified
  - Improve the understanding of the problem
  - Use abstraction to cover a large number of cases

####

## Security problems of multithreaded programs
### Security problems of multithreaded programs
  - There are private (_high_) and public (_low_) variables \pause
  - The attacker can observe low-level variables \pause
  - Sequential:
    - explicit flows: `lo := hi`
    - implicit flows: `if hi then lo := 1 else lo := 0`
  - Concurrent:
    - internal timing leak: \newline `if hi {sleep(100)}; lo := 1 || sleep(50); lo := 0`
    - other example: `hi := 0; lo = hi || hi := private-data` \pause
  - External timing leaks are not covered \pause
  - Advantages of formal methods
    - Applicable on a wide rage of schedulers and bytecode
    - Verification without running the program

####
    
# Discussion of a solution
### Discussion of a solution
  - Syntax & Semantics of multithreaded programs
    - Program
    - State & Security environment
    - History & Scheduler
  - Type system & it's soundness
  - The \texttt{next} function
  - Concrete instantiation
    - Tansfer rules
    - Defining the \texttt{next} function

####
    
## Syntax & Semantics of multithreaded programs
### Program
We have a set of sequential Instructions $SeqIns$ and a primitive
\texttt{start} _pc_ that spawns a new thread. \pause

\begin{definition}[Program P]
  \begin{enumerate}
  \item A set of program points $\mathcal{P}$, with a distinguised entry point \texttt{1} and exit point \texttt{exit}
  \item A map from $\mathcal{P}$ to $Ins$, where $Ins = SeqIns \cup \{start pc\}$ and $pc \in \mathcal{P} \setminus \{\mathtt{stop}\}$.
        This map is refered to as P[i].
  \end{enumerate}
\end{definition} \pause

Further, a relation $\mapsto \subseteq \mathcal{P} \times \mathcal{P}$ that describes possible successor instructions
and it's reflexive and transitive closure $\mapsto^*$.

####

## Syntax & Semantics of multithreaded programs
### State
We have a set of local states, \texttt{LocState} and a global memory \texttt{GMemory}.
In Addition we have a set of thread identifiers \texttt{Thread}. \pause

\begin{definition}[State]
  \begin{enumerate}
  \item \texttt{SeqState} is a product \texttt{LocState} $\times$ \texttt{GMemory}
  \item \texttt{ConcState} is a product (\texttt{Thread} $\rightharpoonup$ \texttt{LocState}) $\times$ \texttt{GMemory}
  \end{enumerate}
\end{definition} \pause

Accessors for a state $s$:

  - s.lst and s.gmem are projections on the first and second component
  - s.act is the set of active threads
  - s.pc(tid) retrieves the current program point of the thread tid

####
  
## Syntax & Semantics of multithreaded programs
### Security environment
We assume a set of levels \texttt{Level} = \{_low_, _high_\} where _low_ < _high_
with an attacker on level _low_. \pause

\begin{definition}[Security environment]
   \begin{enumerate}
   \item A function $se : \mathcal{P} \rightarrow \mathtt{Level}$
   \item A program point $i \in \mathcal{P}$ is:
     \begin{itemize}
     \item low if $se(i) = low$, written $L(i)$
     \item high if $se(i) = high$, written $H(i)$
     \item always high if $\forall j \in \mathcal{P} . (i \mapsto^* j) \rightarrow se(j) = high$, written $AH(i)$
     \end{itemize}
   \end{enumerate}
\end{definition} \pause

Now we classify threads in (where s is a \texttt{ConcState}):
\begin{align*}
s.lowT &= \{tid \in s.act\ |\ L(s.pc(tid))\} \\
s.highT &= \{tid \in s.act\ |\ H(s.pc(tid))\} \\
s.ahighT &= \{tid \in s.act\ |\ AH(s.pc(tid))\} \\
s.hidT &= \{tid \in s.act\ |\ H(s.pc(tid)) \land \lnot AH(s.pc(tid))\} 
\end{align*}

####

## Syntax & Semantics of multithreaded programs
### History & Scheduler
\begin{definition}[History]
A History \texttt{History} is a list of pairs $(tid, l)$, where tid $\in$ \texttt{Thread}
and $l \in$ \texttt{Level}.
\end{definition} \pause

\begin{definition}[Scheduler]
A scheduler is a function $pickt : ConcState \times History \rightharpoonup Thread$
that statisfies these conditions:
   \begin{enumerate}
   \item Always picks active threads
   \item if s.hidT $\neq \emptyset$ then pick(s, h) $\in$ s.hightT
   \item Only uses low names and the low part of the history to pick a low thread
   \end{enumerate}
\end{definition}

####

## Type system & it's soundness
### Type system
\texttt{LType} is a poset ($\leq$ is reflexive, antisymmetric, transitiv) of local types.
\newline\newline
Intuition of the type judgements: $se, i \vdash s \Rightarrow t$ means if executing
program point $i$ the type changes from $s$ to $t$ w.r.t a security environment $se$. \pause

\begin{definition}[Typable program]
A program is typable (written $se, \mathcal{S} \vdash P$) if
  \begin{enumerate}
  \item for all initial program points holds $\mathcal{S}(i) = t_{init}$ and
  \item $\forall i, j \in \mathcal{P}: (i \mapsto j) \rightarrow \exists s \in \mathtt{LType} \ . \ se, i \vdash \mathcal{S}(i) \Rightarrow s \land \mathcal{S}(j) \leq s$
  \end{enumerate}
where $\mathcal{S} : \mathcal{P} \rightarrow \mathtt{LType}$ and $se$ a security environment.
\end{definition}

####

## Type system & it's soundness
### Soundness of the type system
\begin{definition}[Noninterfering program]
$\sim_g$ is a indistinguishability relation on global memories. A program is noninterfering iff for all global memories
$\mu_1, \mu_1', \mu_2, \mu_2'$ the following holds
\[(\mu_1 \sim_g \mu_2 \land P,\mu_1 \Downarrow \mu_1' \land P, \mu_2 \Downarrow \mu_2') \rightarrow \mu_1' \sim_g \mu_2'\]
\end{definition} \pause

\begin{theorem}
If the scheduler is secure and $se, \mathcal{S} \vdash P$, then P is noninterfering
\end{theorem}

Due to this theorem it is possible to typecheck the bytecode (which was compiled type-preserving)
to proof the non-existence of internal timing leaks. \pause

The proof is not part of this presentation, but I'll show the \texttt{next} function
on which the proof relies.

####

## The next function
### The next function
If the execution of program point $i$ results in a high thread, the
function $\mathtt{next}: \mathcal{P} \rightharpoonup \mathcal{P}$ calculates the program point in which the
thread becomes visible again. \pause

The \texttt{next} function has to fulfill the following properties:
\footnotesize
\begin{align}
&Dom(next) = \{i \in \mathcal{P}\ |\ H(i) \land \neg AH(i)\} \\
&i, j \in Dom(next) \land i \mapsto j \Rightarrow next(i) = next(j) \\
&i \in Dom(next) \land L(j) \land i \mapsto j \Rightarrow next(i) = j \\
&j, k \in Dom(next) \land L(i) \land i \mapsto j \land i \mapsto k \land j \neq k \Rightarrow next(j) = next(k) \\
&i, j \in Dom(next) \land L(k) \land i \mapsto j \land i \mapsto k \land j \neq k \Rightarrow next(j) = k
\end{align}

####

## Instantiation
### Source and target language
  - Simple langugage with `if`, `;`, `:=`, `while` and `fork` \pause
  - Assembly 
    - `push n` -- push value on the stack
    - `load x` -- push value of variable on the stack
    - `store x` -- store first element of the stack in x
    - `goto j` / `ifeq j` -- un-/conditional jump to j
    - `start j` -- create a new thread starting in j

####
    
## Instantiation
### Transfer rules
$\mathtt{LType} = Stack(\mathtt{Level})$ \pause

\begin{prooftree}
\AxiomC{$P[i] = store\ x$}
\AxiomC{$se(i) \sqcup k \leq \Gamma(x)$}
\BinaryInfC{$se, i \vdash_{seq} k :: st \Rightarrow st$}
\end{prooftree}

\begin{prooftree}
\AxiomC{$P[i] = ifeq\ j$}
\AxiomC{$\forall j' \in reg(i), k \leq se(j')$}
\BinaryInfC{$se, i \vdash_{seq} k :: st \Rightarrow lift_k(st)$}
\end{prooftree}

where $reg : \mathcal{P} \rightharpoonup \mathfrak{P}(\mathcal{P})$ computes the control dependence region.
$lift_k(st)$ is the point-wise extension of $\lambda k' . k \sqcup k'$. $\Gamma(x)$ expresses the chosen security policy by assigning a security level to each variable. \pause

Similar rules have to be established for the other commands of the target language.

####

## Instantiation
### Concurrent extension
The transfer rules are extended by the following rules:

\begin{prooftree}
\AxiomC{P[i] $\in$ SeqIns}
\AxiomC{$se, i \vdash_{seq} s \Rightarrow t$}
\BinaryInfC{$se, i \vdash s \Rightarrow t$}
\end{prooftree}

\begin{prooftree}
\AxiomC{P[i] = \texttt{start} pc}
\AxiomC{$se(i) \leq se(pc)$}
\BinaryInfC{$se, i \vdash s \Rightarrow s$}
\end{prooftree} \pause

We label the program points where control flow can branch or side effects can ocour.

> c ::= [x := e]$^n$ | c;c | [if e then c else c]$^n$ | [while e do c]$^n$ | [fork(c)]$^n$

With this labeling we can define control dependence regions for the source langugage (\texttt{sregion}) and derive
them for the target language (\texttt{tregion}).

####

## Instantiation
### sregion & tregion
\begin{definition}[sregion]
$sregion(n)$ is defined as the set of labels that are inside a branching command $[c]^n$, except those inside \texttt{fork}.
\end{definition} \pause

\begin{definition}[tregion]
$tregion(n)$ is defined for $[c]^n$ as the set of instructions/labels obtained by compiling $[c']^{n'}$ where $n' \in sregion(n)$.
If c is \texttt{while} then $n \in tregion(n)$.
\end{definition} \pause

Excerpt of the compilation function C:

`C(c) = let (lc, T) = S(c, []);` \newline
\hspace*{15mm} `in goto (#T + 2) :: T :: lc :: return` \newline
`S(fork(c), T) = let (lc, T') = S(c, T);` \newline
\hspace*{15mm} `in (start (#T' + 2), T' :: lc :: return)`

####

## Instantiation
### junction points & next function
\begin{definition}[junction point]
For every branching point $[c]^n$ in the source program we define
\begin{align*}
jun(n) = max \{i|i \in tregion(n)\} + 1
\end{align*}
\end{definition} \pause

To identify the outermost branching points that involves secrets we extend the type system. A source program
is typeable ($\vdash_\circ c : E$ where E maps labels to security levels) and judgments of the form $\vdash_\alpha [c]^n_{\alpha'} : E$.
One example typing rule ($\circ$ public, $\bullet$ secret):

\begin{prooftree}
\AxiomC{$\vdash e : H$}
\AxiomC{$\vdash_\bullet c :E$}
\AxiomC{$E = lift_H(E, sregion(n))$}
\TrinaryInfC{$\vdash_\circ [while \ e \ do \ c]^n_\bullet : E$}
\end{prooftree} \pause

\begin{definition}[next]
For alle branching program points c such that $\vdash_{\circ}[n]^n_\bullet$ $next$ is defined as
$\forall k \in tregion(n)\ . \ next(k) = jun(n)$.
\end{definition}

####
    
# Other/related solutions
### Other/related solutions
  - Protection/hiding based approaches
    - Volpano & Smith \cite{SmithVolpano1998}\cite{SmithVolpano1999}\cite{SmithVolpano1996} use a \texttt{protect(c)} primitive
    - Russo & Sabelfeld \cite{RussoSabelfeld2006} use \texttt{hide} and \texttt{unhide} primitives
  - Low-determinism approaches
    - Zdancewic and Myres \cite{Zdancewic} disallow races on public data
  - External-timing based approaches
    - here the attacker is more powerful: he can measure execution time
    - this causes much more restrictiveness (e.g. loops with secret guards are disallowed)

####
    
## Other/related solutions
### Comparison with Zdancewi and Myres\cite{Zdancewic}
  - Introduces a relative complex language $\lambda^{PAR}_{SEC}$
  - Also uses a type system to enforce security
  - Uses the same notion of noninterference
  - Observational determinism is defined as the indistinguishability of memory access traces
    \begin{align*}(m \approx_\zeta m' \land m  \Downarrow T \land m' \Downarrow T') \Rightarrow T \approx_\zeta T'\end{align*}
    Thus it rejects Programs like `lo := 1 || lo := 0`
  - In contrast to the paper discussed here, $\lambda^{PAR}_{SEC}$ provides
    support for synchronization using *join patterns*

####
    
# Conclusion / Outlook
## Outlook
### Adaption to the JVM
  - JVML's sequential type system is compatible with bytecode verifikation, thus it's compatible with the concurrent type system.
  - The scheduler is mostly left unspecified, thus introducing a secure scheduler is possible. \pause
  - Issues
    - Method calls have a big-step semantic
    - This approach does not deal with synchronization

####

## Conclusion
### Conclusion
  - Proof of noninterference for a concurrent low-level language
  - Proof of type-preserving compilation in context of concurrency \pause
  - Scheduler is driven by the security environment
  - Independent of the scheduling algorithm \pause
  - No useful secure programs are rejected \pause
  - No need to trust the compiler, checking can be done at target level (without running the program) \pause
  - Programmer does not need to know about internal timing leaks \pause
  - No restrictions on dynamic thread creation \pause
  - What needs to be done? Extension for real world languages e.g. adding support for synchronization

####
  
# Bibliography
### Bibliography
%FIXME: allowframebreaks
\bibliographystyle{plain}
\bibliography{bibliography}{}

####
