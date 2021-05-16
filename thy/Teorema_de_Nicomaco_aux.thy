chapter \<open>Sums of Powers, Polynomials\<close>

theory Teorema_de_Nicomaco_aux 
imports Main 
begin

subsection \<open>Sums of Powers\<close>

text \<open>We consider sums of consecutive powers: 
  $S_p(n) = \sum_{k=1}^n{k^p}$.

  $\rhd$ Define a corresponding function @{term "S p n"}.\<close>

definition S :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "S p n \<equiv> \<Sum>k=1..n. k^p"

text \<open>Hint: exponentiation and summation functions are already available
  in Isabelle/HOL.

  \medskip

  Clearly, $S_0(n) = n$.  It is also well-known that 
  $S_1(n) = \frac{n^2 + n}{2}$.

  $\rhd$ Prove these identities.\<close>

lemma "S 0 n = n"
  by (simp add: S_def)

lemma gauss: "2 * S 1 n = n^2 + n"
  by (induct n) (auto simp add: S_def power2_eq_square)

thm power2_eq_square
(* ?a\<^sup>2 = ?a * ?a *)

text \<open>At this point, we might suspect that $S_p(n)$ is a polynomial
  in $n$ with rational coefficients.

  $\rhd$ Verify this conjecture for $p=2$, i.e., find $k > 0$ and a
  polynomial $\mathit{poly}$ in $n$ so that 
  $k \cdot S_2(n) = \mathit{poly}$. Prove the resulting identity. \<close>

lemma "6 * S 2 n = 2*n^3 + 3*n^2 + n"    
  by (induct n) (auto simp add: S_def 
                                algebra_simps 
                                power2_eq_square 
                                power3_eq_cube)

text \<open>Hint: useful simplification rules for addition and multiplication
  are available as @{text "algebra_simps"}. The \emph{Find theorems} 
  command can be used to discover further lemmas.

  \medskip

  \ begin{figure}[t]
  \includegraphics[width=\textwidth]{CubeSquare_600}
  \caption{Visualization of Nicomachus's theorem}
  \end{figure}

  For $p=3$, our conjecture follows from the astonishing identity
  $\sum_{k=1}^n{k^3} = (\sum_{k=1}^n{k})^2$, which is known as
  \emph{Nicomachus's theorem}.

  $\rhd$ Prove Nicomachus's theorem.\<close>

lemma l1: "4 * S 3 n = (n^2 + n)^2"
  by (induct n) (auto simp add: S_def 
                                algebra_simps 
                                power2_eq_square 
                                power3_eq_cube)

lemma l2: "4 * (m::nat) = (2 * n)^2 \<Longrightarrow> m = n^2"
  by (simp add: power2_eq_square)

theorem "S 3 n = (S 1 n)^2"
  by (simp only: l1 l2 gauss)

text \<open>Before we could prove our conjecture for arbitrary~$p$ (which we
  will not do as part of this assignment, but search for 
  \emph{Faulhaber's formula} if you want to know more), we need to 
  define polynomials.\<close>

subsection \<open>Polynomials\<close>

text \<open>A polynomial in one variable can be given by the list of its
  coefficients: e.g., $[0, \frac{1}{6}, \frac{1}{3}, \frac{1}{2}]$
  represents the polynomial $\frac{1}{2}x^3 + \frac{1}{3}x^2 +
  \frac{1}{6}x + 0$.  (We list coefficients in reverse order, i.e., from
  lower to higher degree.)

  Coefficients may be integers, rationals, reals, etc.  In general, we
  require coefficients to be elements of a commutative ring (cf.\ @{text
  Rings.thy}).

  To every polynomial in one variable we can associate a
  \emph{polynomial function} on the ring of coefficients.  This
  function's value is obtained by substituting its argument for the
  polynomial's variable, i.e., by evaluating the polynomial.

  $\rhd$ Define a function @{term "poly cs x"} so that $\mathit{poly}\
  [c_0, c_1, \dots, c_n]\ x = c_n\underbrace{x\cdot\dots\cdot
  x}_{\small \mbox{$n$ factors}} + \dots + c_1x + c_0$.
\<close>

fun poly :: "'a :: comm_ring list \<Rightarrow> 'a :: comm_ring \<Rightarrow> 'a :: comm_ring" 
  where
  "poly [] _     = 0"
| "poly (c#cs) x = c + x * poly cs x"

text \<open>$\rhd$ Define a function @{term "poly_plus p q"} that computes the
  sum of two polynomials.\<close>

fun poly_plus :: "'a :: comm_ring list 
                  \<Rightarrow> 'a :: comm_ring list 
                  \<Rightarrow> 'a :: comm_ring list" where
  "poly_plus p []          = p"
| "poly_plus [] q          = q"
| "poly_plus (p#ps) (q#qs) = (p + q) # poly_plus ps qs"

text \<open>$\rhd$ Prove correctness of @{term poly_plus}.\<close>

lemma poly_plus_correct: "poly (poly_plus p q) x = poly p x + poly q x"
  by (induct p q rule: poly_plus.induct) (auto simp add: algebra_simps)

text \<open>
Hint: Isabelle provides customized induction rules for recursive
functions, e.g., @{text poly_plus.induct}.  See the \emph{Tutorial on
Function Definitions} for details.

\medskip

$\rhd$ Define a function @{term "poly_times p q"} that computes the
product of two polynomials.
\<close>

fun poly_times :: "'a :: comm_ring list 
                  \<Rightarrow> 'a :: comm_ring list 
                  \<Rightarrow> 'a :: comm_ring list" where
  "poly_times [] _ = []"
| "poly_times (p#ps) q = poly_plus (map ((*) p) q) 
                                   (poly_times ps (0 # q))"

text \<open>$\rhd$ Prove correctness of @{term poly_times}. \<close>

lemma poly_map_times: "poly (map ((*) c) p) x = c * poly p x"
  by (induct p) (auto simp add: algebra_simps)

lemma "poly (poly_times p q) x = poly p x * poly q x"
  by (induct p q rule: poly_times.induct) 
     (auto simp add: algebra_simps 
                     poly_plus_correct 
                     poly_map_times)

(*<*)end(*>*)
