A stronger form of Yamamoto’s theorem on singular values
========================================================

Soumyashant Nayak Statistics and Mathematics Unit  
Indian Statistical Institute  
8th Mile, Mysore Road  
RVCE Post, Bengaluru  
Karnataka - 560 059, India [soumyashant@isibang.ac.in](mailto:soumyashant@isibang.ac.in)

###### Abstract.

For a matrix T∈Mm​(ℂ)𝑇subscript𝑀𝑚ℂT\\in M\_{m}(\\mathbb{C}), let |T|:=T∗​Tassign𝑇superscript𝑇𝑇|T|:=\\sqrt{T^{\*}T}. For A∈Mm​(ℂ)𝐴subscript𝑀𝑚ℂA\\in M\_{m}(\\mathbb{C}), we show that the matrix sequence {|An|1n}n∈ℕsubscriptsuperscriptsuperscript𝐴𝑛1𝑛𝑛ℕ\\big{\\{}|A^{n}|^{\\frac{1}{n}}\\big{\\}}\_{n\\in\\mathbb{N}} converges to a positive-semidefinite matrix H𝐻H whose jthsuperscript𝑗thj^{\\textrm{th}}\-largest eigenvalue is equal to the jthsuperscript𝑗thj^{\\textrm{th}}\-largest eigenvalue-modulus of A𝐴A (for 1≤j≤m1𝑗𝑚1\\leq j\\leq m). In fact, we give an explicit description of the spectral projections of H𝐻H in terms of the eigenspaces of the diagonalizable part of A𝐴A in its Jordan-Chevalley decomposition. This gives us a stronger form of Yamamoto’s theorem which asserts that limn→∞sj​(An)1nsubscript→𝑛subscript𝑠𝑗superscriptsuperscript𝐴𝑛1𝑛\\lim\_{n\\to\\infty}s\_{j}(A^{n})^{\\frac{1}{n}} is equal to the jthsuperscript𝑗thj^{\\textrm{th}}\-largest eigenvalue-modulus of A𝐴A, where sj​(An)subscript𝑠𝑗superscript𝐴𝑛s\_{j}(A^{n}) denotes the jthsuperscript𝑗thj^{\\textrm{th}}\-largest singular value of Ansuperscript𝐴𝑛A^{n}. Moreover, we also discuss applications to the asymptotic behaviour of the matrix exponential function, t↦et​Amaps-to𝑡superscript𝑒𝑡𝐴t\\mapsto e^{tA}.

  

Keywords: Singular values, Yamamoto’s theorem, spectral-radius formula, matrix exponential function MSC2010 subject classification: 15A60, 15A90, 47D06

1\. Introduction
----------------

The well-known spectral radius formula for a matrix A𝐴A,

|     |     |     |
| --- | --- | --- |
|     | ρ​(A)\=limn→∞‖An‖1n,𝜌𝐴subscript→𝑛superscriptnormsuperscript𝐴𝑛1𝑛\\rho(A)=\\lim\_{n\\to\\infty}\\\|A^{n}\\\|^{\\frac{1}{n}}, |     |

provides insight into the asymptotic behaviour of powers of matrices. Building upon the work of Gautschi (see \[[4](https://ar5iv.labs.arxiv.org/html/2303.01252#bib.bib4)\
\], \[[5](https://ar5iv.labs.arxiv.org/html/2303.01252#bib.bib5)\
\]), Yamamoto considerably refined this result by proving the following theorem.

Yamamoto’s theorem (see \[[9](https://ar5iv.labs.arxiv.org/html/2303.01252#bib.bib9)\
, Theorem 1\]) Let A𝐴A be a matrix in Mm​(ℂ)subscript𝑀𝑚ℂM\_{m}(\\mathbb{C}) and |λj|​(A)subscript𝜆𝑗𝐴|\\lambda\_{j}|(A) denote the jthsuperscript𝑗thj^{\\textrm{th}}\-largest number in the list of modulus of eigenvalues of A𝐴A (counted with multiplicity). Then

|     |     |     |
| --- | --- | --- |
|     | limn→∞sj​(An)1n\=\|λj\|​(A),subscript→𝑛subscript𝑠𝑗superscriptsuperscript𝐴𝑛1𝑛subscript𝜆𝑗𝐴\\lim\_{n\\to\\infty}s\_{j}(A^{n})^{\\frac{1}{n}}=\|\\lambda\_{j}\|(A), |     |

where sj​(An)subscript𝑠𝑗superscript𝐴𝑛s\_{j}(A^{n}) denotes the jthsuperscript𝑗thj^{\\textrm{th}}\-largest singular value of Ansuperscript𝐴𝑛A^{n}. Note that the spectral radius formula corresponds to the case j\=1𝑗1j=1 as s1​(T)\=‖T‖subscript𝑠1𝑇norm𝑇s\_{1}(T)=\\|T\\| for any T∈Mm​(ℂ)𝑇subscript𝑀𝑚ℂT\\in M\_{m}(\\mathbb{C}). In \[[7](https://ar5iv.labs.arxiv.org/html/2303.01252#bib.bib7)\
\], Mathias provides an elegant proof of the above-mentioned result using the interlacing properties of singular values for principal diagonal blocks of a matrix. In \[[8](https://ar5iv.labs.arxiv.org/html/2303.01252#bib.bib8)\
\], Tam and Huang generalize the result to the context of real semisimple Lie groups, with the original result corresponding to the case of S​Ln​(ℂ)𝑆subscript𝐿𝑛ℂSL\_{n}(\\mathbb{C}).

For an operator T𝑇T acting on a Hilbert space, we use the notation |T|:=T∗​Tassign𝑇superscript𝑇𝑇|T|:=\\sqrt{T^{\*}T}. In this article, our main goal is to prove a stronger form of Yamamoto’s theorem by showing the convergence of the matrix sequence {|An|1n}n∈ℕsubscriptsuperscriptsuperscript𝐴𝑛1𝑛𝑛ℕ\\{|A^{n}|^{\\frac{1}{n}}\\}\_{n\\in\\mathbb{N}} for every m×m𝑚𝑚m\\times m complex matrix A𝐴A. The Main Result (see Theorem [3.8](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.Thmthm8 "Theorem 3.8. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")
) Let A∈Mm​(ℂ)𝐴subscript𝑀𝑚ℂA\\in M\_{m}(\\mathbb{C}) and {a1,…,ak}subscript𝑎1…subscript𝑎𝑘\\{a\_{1},\\ldots,a\_{k}\\} be the set of modulus of eigenvalues of A𝐴A such that 0≤a1<a2<⋯<ak0subscript𝑎1subscript𝑎2⋯subscript𝑎𝑘0\\leq a\_{1}<a\_{2}<\\cdots<a\_{k}. Let A\=D+N𝐴𝐷𝑁A=D+N be the Jordan-Chevalley decomposition of A𝐴A into its commuting diagonalizable and nilpotent parts (D,N𝐷𝑁D,N, respectively). For 1≤j≤k1𝑗𝑘1\\leq j\\leq k, let Ejsubscript𝐸𝑗E\_{j} be the orthogonal projection onto the subspace of ℂmsuperscriptℂ𝑚\\mathbb{C}^{m} spanned by the eigenvectors of D𝐷D corresponding to eigenvalues with modulus less than or equal to ajsubscript𝑎𝑗a\_{j}, and set E0:=0assignsubscript𝐸00E\_{0}:=0. Then the following assertions hold:

*   (i)
    
    The sequence {|An|1n}n∈ℕsubscriptsuperscriptsuperscript𝐴𝑛1𝑛𝑛ℕ\\{|A^{n}|^{\\frac{1}{n}}\\}\_{n\\in\\mathbb{N}} converges to the positive-semidefinite matrix ∑i\=1kaj​(Ej−Ej−1).superscriptsubscript𝑖1𝑘subscript𝑎𝑗subscript𝐸𝑗subscript𝐸𝑗1\\sum\_{i=1}^{k}a\_{j}(E\_{j}-E\_{j-1}).
    
*   (ii)
    
    A non-zero vector x→∈ℂm→𝑥superscriptℂ𝑚\\vec{x}\\in\\mathbb{C}^{m} is in ran​(Ej)\\ran​(Ej−1)\\ransubscript𝐸𝑗ransubscript𝐸𝑗1\\mathrm{ran}(E\_{j})\\backslash\\mathrm{ran}(E\_{j-1}) if and only if limn→∞‖An​x→‖1n\=aj.subscript→𝑛superscriptnormsuperscript𝐴𝑛→𝑥1𝑛subscript𝑎𝑗\\lim\_{n\\to\\infty}\\|A^{n}\\vec{x}\\|^{\\frac{1}{n}}=a\_{j}.
    
*   (iii)
    
    The set ran​(Ej)\\ran​(Ej−1)\\ransubscript𝐸𝑗ransubscript𝐸𝑗1\\mathrm{ran}(E\_{j})\\backslash\\mathrm{ran}(E\_{j-1}) is invariant under the action of Aksuperscript𝐴𝑘A^{k} for every k∈ℕ𝑘ℕk\\in\\mathbb{N}.
    

Since the solution of the system of coupled ordinary differential equations,

|     |     |     |
| --- | --- | --- |
|     | d​X→​(t)d​t\=A​X→​(t),X→:ℝ→ℂm,:𝑑→𝑋𝑡𝑑𝑡𝐴→𝑋𝑡→𝑋→ℝsuperscriptℂ𝑚\\frac{d\\vec{X}(t)}{dt}=A\\vec{X}(t),\\;\\vec{X}:\\mathbb{R}\\to\\mathbb{C}^{m}, |     |

is given by X→​(t)\=eA​t​X→​(0)→𝑋𝑡superscript𝑒𝐴𝑡→𝑋0\\vec{X}(t)=e^{At}\\vec{X}(0), the asymptotic behaviour of the matrix exponential function, t↦et​Amaps-to𝑡superscript𝑒𝑡𝐴t\\mapsto e^{tA}, has traditionally been of great interest. In §[4](https://ar5iv.labs.arxiv.org/html/2303.01252#S4 "4. Applications to linear systems of ordinary differential equations ‣ A stronger form of Yamamoto’s theorem on singular values")
, we make some novel observations in this regard (cf. \[[3](https://ar5iv.labs.arxiv.org/html/2303.01252#bib.bib3)\
, Chapter 4\]). Noting that the diagonalizable part of eAsuperscript𝑒𝐴e^{A} is eDsuperscript𝑒𝐷e^{D}, as a corollary of Theorem [3.8](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.Thmthm8 "Theorem 3.8. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")
, we show that limt→∞|et​A|1tsubscript→𝑡superscriptsuperscript𝑒𝑡𝐴1𝑡\\lim\_{t\\to\\infty}|e^{tA}|^{\\frac{1}{t}} exists and provide an explicit description of the spectral projections of the limit (see Theorem [4.1](https://ar5iv.labs.arxiv.org/html/2303.01252#S4.Thmthm1 "Theorem 4.1. ‣ 4. Applications to linear systems of ordinary differential equations ‣ A stronger form of Yamamoto’s theorem on singular values")
). Furthermore, we show that limt→∞‖X→​(t)‖1tsubscript→𝑡superscriptnorm→𝑋𝑡1𝑡\\lim\_{t\\to\\infty}\\|\\vec{X}(t)\\|^{\\frac{1}{t}} exists and compute its value, which provides precise information about the growth of the norm of the solution vector, ‖X→​(t)‖norm→𝑋𝑡\\|\\vec{X}(t)\\|, as t→∞→𝑡t\\to\\infty. This strengthens Theorem 4.5-(a) in \[[3](https://ar5iv.labs.arxiv.org/html/2303.01252#bib.bib3)\
\].

Note that the Jordan-Chevalley decomposition of A𝐴A is an algebraic fact and does not care about the inner product on ℂmsuperscriptℂ𝑚\\mathbb{C}^{m} where as the adjoint operation is intimately connected with the inner product (and thereby, the Hilbert space structure). Our result shows that the asymptotic behaviour of {|An|1n}n∈ℕsubscriptsuperscriptsuperscript𝐴𝑛1𝑛𝑛ℕ\\{|A^{n}|^{\\frac{1}{n}}\\}\_{n\\in\\mathbb{N}} (and |et​A|1tsuperscriptsuperscript𝑒𝑡𝐴1𝑡|e^{tA}|^{\\frac{1}{t}}) is dictated by the algebraic properties of A𝐴A.

Let ℳℳ\\mathscr{M} be a type I​I1𝐼subscript𝐼1II\_{1} von Neumann factor. In \[[6](https://ar5iv.labs.arxiv.org/html/2303.01252#bib.bib6)\
\], using tools from free probability theory and ultrapower techniques, it was proved by Haagerup and Schultz that the sequence {|Tn|1n}n∈ℕsubscriptsuperscriptsuperscript𝑇𝑛1𝑛𝑛ℕ\\{|T^{n}|^{\\frac{1}{n}}\\}\_{n\\in\\mathbb{N}} converges in the strong-operator topology (and being a norm-bounded sequence, in the ultra-strong topology). Furthermore, an elementary example (due to Voiculescu, see \[[6](https://ar5iv.labs.arxiv.org/html/2303.01252#bib.bib6)\
, Example 8.4\]) is given of a weighted shift operator S𝑆S on an infinite-dimensional Hilbert space such that the sequence {|Sn|1n}n∈ℕsubscriptsuperscriptsuperscript𝑆𝑛1𝑛𝑛ℕ\\{|S^{n}|^{\\frac{1}{n}}\\}\_{n\\in\\mathbb{N}} does not converge in the strong-operator topology. It is no surprise that the matrix case (which corresponds to finite-dimensional type I𝐼I factors) affords substantial simplifications and as mentioned above, we are able to obtain precise information about the limit matrix in terms of the diagonalizable part of the Jordan-Chevalley decomposition of A𝐴A.

2\. Preparatory results
-----------------------

In this section, we organize some preparatory results on sequences of real numbers, and singular values of matrices, en route to Theorem [3.8](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.Thmthm8 "Theorem 3.8. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")
. First we compile a list of notation used in this article for the reader’s quick reference.

Notation:

*   •
    
    We use the standard notation ℕ,ℝ,ℂℕℝℂ\\mathbb{N},\\mathbb{R},\\mathbb{C}, respectively, to denote the set of natural numbers, real numbers, complex numbers, respectively.
    
*   •
    
    The real part of a complex number λ𝜆\\lambda is denoted by ℜ⁡λ𝜆\\Re\\lambda.
    
*   •
    
    For a matrix T∈Mm​(ℂ)𝑇subscript𝑀𝑚ℂT\\in M\_{m}(\\mathbb{C}), we denote its range in ℂmsuperscriptℂ𝑚\\mathbb{C}^{m} by ran​(T)ran𝑇\\mathrm{ran}(T). The multiset of eigenvalues of T𝑇T is denoted by λ​(T)𝜆𝑇\\lambda(T), and the multiset of modulus of eigenvalues of T𝑇T is denoted by |λ|​(T)𝜆𝑇|\\lambda|(T). The jthsuperscript𝑗thj^{\\textrm{th}}\-largest singular value of T𝑇T is denoted by sj​(T)subscript𝑠𝑗𝑇s\_{j}(T), and the jthsuperscript𝑗thj^{\\textrm{th}}\-largest element of |λ|​(T)𝜆𝑇|\\lambda|(T) is denoted by |λj|​(T)subscript𝜆𝑗𝑇|\\lambda\_{j}|(T).
    
    (A multiset is a collection of objects in which elements may occur more than once but finitely many times, that is, a set with a finite multiplicity function for each of its elements. The underlying set of a multiset is said to be its support. See \[[2](https://ar5iv.labs.arxiv.org/html/2303.01252#bib.bib2)\
    \] for a quick introduction to multiset theory.)
    

### 2.1. Some elementary results on sequences of real numbers

###### Lemma 2.1.

Let k𝑘k be a fixed positive integer. Then

|     |     |     |
| --- | --- | --- |
|     | limn→∞(nk)n\=1.subscript→𝑛𝑛binomial𝑛𝑘1\\lim\_{n\\to\\infty}\\sqrt\[n\]{\\binom{n}{k}}=1. |     |

###### Proof.

Note that limn→∞|n−a|n\=1subscript→𝑛𝑛𝑛𝑎1\\lim\_{n\\to\\infty}\\sqrt\[n\]{|n-a|}=1 and limn→∞an\=1subscript→𝑛𝑛𝑎1\\lim\_{n\\to\\infty}\\sqrt\[n\]{a}=1 for all a\>0𝑎0a>0. Thus

|     |     |     |
| --- | --- | --- |
|     | limn→∞(nk)n\=limn→∞nn​\|n−1\|n​⋯​\|n−k+1\|n/k!n\=1.subscript→𝑛𝑛binomial𝑛𝑘subscript→𝑛𝑛𝑛𝑛𝑛1⋯𝑛𝑛𝑘1𝑛𝑘1\\lim\_{n\\to\\infty}\\sqrt\[n\]{\\binom{n}{k}}=\\lim\_{n\\to\\infty}\\sqrt\[n\]{n}\\sqrt\[n\]{\|n-1\|}\\cdots\\sqrt\[n\]{\|n-k+1\|}/\\sqrt\[n\]{k!}=1. |     |

∎

###### Lemma 2.2.

Let {a1,n}n∈ℕ,…,{ak,n}n∈ℕsubscriptsubscript𝑎1𝑛𝑛ℕ…subscriptsubscript𝑎𝑘𝑛𝑛ℕ\\{a\_{1,n}\\}\_{n\\in\\mathbb{N}},\\ldots,\\{a\_{k,n}\\}\_{n\\in\\mathbb{N}} be k𝑘k\-many sequences of non-negative real numbers and let bn:=∑i\=1kai,nassignsubscript𝑏𝑛superscriptsubscript𝑖1𝑘subscript𝑎𝑖𝑛b\_{n}:=\\sum\_{i=1}^{k}a\_{i,n}. Then

|     |     |     |
| --- | --- | --- |
|     | lim supnbnn≤max1≤i≤k⁡{lim supnai,nn}.subscriptlimit-supremum𝑛𝑛subscript𝑏𝑛subscript1𝑖𝑘subscriptlimit-supremum𝑛𝑛subscript𝑎𝑖𝑛\\limsup\_{n}\\sqrt\[n\]{b\_{n}}\\leq\\max\_{1\\leq i\\leq k}\\big{\\{}\\limsup\_{n}\\sqrt\[n\]{a\_{i,n}}\\big{\\}}. |     |

###### Proof.

We may assume that lim supnai,nn<∞subscriptlimit-supremum𝑛𝑛subscript𝑎𝑖𝑛\\limsup\_{n}\\sqrt\[n\]{a\_{i,n}}<\\infty for all 1≤i≤k1𝑖𝑘1\\leq i\\leq k, as otherwise there is nothing to prove. Consider the power series pi​(z)≡∑ai,n​znsubscript𝑝𝑖𝑧subscript𝑎𝑖𝑛superscript𝑧𝑛p\_{i}(z)\\equiv\\sum a\_{i,n}z^{n} with radius of convergence,

|     |     |     |
| --- | --- | --- |
|     | Ri\=1lim supnai,nn\>0.subscript𝑅𝑖1subscriptlimit-supremum𝑛𝑛subscript𝑎𝑖𝑛0R\_{i}=\\frac{1}{\\limsup\_{n}\\sqrt\[n\]{a\_{i,n}}}>0. |     |

Clearly, the power series p​(z)≡∑bn​zn≡∑i\=1kpi​(z)𝑝𝑧subscript𝑏𝑛superscript𝑧𝑛superscriptsubscript𝑖1𝑘subscript𝑝𝑖𝑧p(z)\\equiv\\sum b\_{n}z^{n}\\equiv\\sum\_{i=1}^{k}p\_{i}(z) converges in the open ball of radius min1≤i≤k⁡{Ri}\>0subscript1𝑖𝑘subscript𝑅𝑖0\\min\_{1\\leq i\\leq k}\\{R\_{i}\\}>0, centred at the origin. Thus the radius of convergence of the power series p𝑝p,

|     |     |     |
| --- | --- | --- |
|     | R\=1lim supnbnn,𝑅1subscriptlimit-supremum𝑛𝑛subscript𝑏𝑛R=\\frac{1}{\\limsup\_{n}\\sqrt\[n\]{b\_{n}}}, |     |

is greater than or equal to min1≤i≤k⁡{Ri}subscript1𝑖𝑘subscript𝑅𝑖\\min\_{1\\leq i\\leq k}\\{R\_{i}\\}. Taking reciprocals, we get the desired result. ∎

###### Lemma 2.3.

Let 0≤a1<…<am0subscript𝑎1…subscript𝑎𝑚0\\leq a\_{1}<\\ldots<a\_{m} and t1,t2,…,tm∈\[0,∞)subscript𝑡1subscript𝑡2…subscript𝑡𝑚0t\_{1},t\_{2},\\ldots,t\_{m}\\in\[0,\\infty) with tm≠0subscript𝑡𝑚0t\_{m}\\neq 0. Then limn→∞(∑i\=1mti​ain)1n\=amsubscript→𝑛superscriptsuperscriptsubscript𝑖1𝑚subscript𝑡𝑖superscriptsubscript𝑎𝑖𝑛1𝑛subscript𝑎𝑚\\lim\_{n\\to\\infty}\\big{(}\\sum\_{i=1}^{m}t\_{i}a\_{i}^{n}\\big{)}^{\\frac{1}{n}}=a\_{m}.\
\
###### Proof.\
\
Let C:=max1≤i≤m⁡{titm}≥1assign𝐶subscript1𝑖𝑚subscript𝑡𝑖subscript𝑡𝑚1C:=\\max\_{1\\leq i\\leq m}\\{\\frac{t\_{i}}{t\_{m}}\\}\\geq 1. Note that tm​amn≤∑i\=1mti​ain≤m​C​tm​amn,subscript𝑡𝑚superscriptsubscript𝑎𝑚𝑛superscriptsubscript𝑖1𝑚subscript𝑡𝑖superscriptsubscript𝑎𝑖𝑛𝑚𝐶subscript𝑡𝑚superscriptsubscript𝑎𝑚𝑛t\_{m}a\_{m}^{n}\\leq\\sum\_{i=1}^{m}t\_{i}a\_{i}^{n}\\leq mCt\_{m}a\_{m}^{n}, so that\
\
|     |     |     |\
| --- | --- | --- |\
|     | am​(tm)1n≤(∑i\=1mti​ain)1n≤am​(m​C​tm)1n,∀n∈ℕ.formulae-sequencesubscript𝑎𝑚superscriptsubscript𝑡𝑚1𝑛superscriptsuperscriptsubscript𝑖1𝑚subscript𝑡𝑖superscriptsubscript𝑎𝑖𝑛1𝑛subscript𝑎𝑚superscript𝑚𝐶subscript𝑡𝑚1𝑛for-all𝑛ℕa\_{m}(t\_{m})^{\\frac{1}{n}}\\leq(\\sum\_{i=1}^{m}t\_{i}a\_{i}^{n})^{\\frac{1}{n}}\\leq a\_{m}(mCt\_{m})^{\\frac{1}{n}},\\;\\;\\;\\forall n\\in\\mathbb{N}. |     |\
\
The assertion follows from the fact that limn→∞tm1n\=limn→∞(m​C​tm)1n\=1subscript→𝑛superscriptsubscript𝑡𝑚1𝑛subscript→𝑛superscript𝑚𝐶subscript𝑡𝑚1𝑛1\\lim\_{n\\to\\infty}t\_{m}^{\\frac{1}{n}}=\\lim\_{n\\to\\infty}(mCt\_{m})^{\\frac{1}{n}}=1 and the sandwich lemma. ∎\
\
### 2.2. Singular values of matrices\
\
The usual matrix norm is denoted by ∥⋅∥\\|\\cdot\\|. Since Mm​(ℂ)subscript𝑀𝑚ℂM\_{m}(\\mathbb{C}) is a finite-dimensional normed linear space, all norms are equivalent, and the notion of norm-convergence used is immaterial. Most of the results in this subsection follow from standard techniques discussed in the masterful account of the subject of matrix analysis in \[[1](https://ar5iv.labs.arxiv.org/html/2303.01252#bib.bib1)\
\].\
\
###### Lemma 2.4.\
\
Let {Hn}n∈ℕsubscriptsubscript𝐻𝑛𝑛ℕ\\{H\_{n}\\}\_{n\\in\\mathbb{N}} be a sequence of Hermitian matrices in Mm​(ℂ)subscript𝑀𝑚ℂM\_{m}(\\mathbb{C}) converging to H𝐻H in norm. Then sj​(Hn)→sj​(H)→subscript𝑠𝑗subscript𝐻𝑛subscript𝑠𝑗𝐻s\_{j}(H\_{n})\\to s\_{j}(H), where sj​(⋅)subscript𝑠𝑗⋅s\_{j}(\\cdot) denotes the jthsuperscript𝑗thj^{\\textrm{th}} singular value for 1≤j≤m1𝑗𝑚1\\leq j\\leq m.\
\
###### Proof.\
\
Applying Weyl’s perturbation theorem (see \[[1](https://ar5iv.labs.arxiv.org/html/2303.01252#bib.bib1)\
, Theorem VI.2.1\]), we have\
\
|     |     |     |\
| --- | --- | --- |\
|     | \|sj​(Hn)−sj​(H)\|≤‖Hn−H‖,subscript𝑠𝑗subscript𝐻𝑛subscript𝑠𝑗𝐻normsubscript𝐻𝑛𝐻\|s\_{j}(H\_{n})-s\_{j}(H)\|\\leq\\\|H\_{n}-H\\\|, |     |\
\
which proves the assertion. ∎\
\
###### Proposition 2.5.\
\
Let A∈Mm​(ℂ)𝐴subscript𝑀𝑚ℂA\\in M\_{m}(\\mathbb{C}) with eigenvalues λ1,…,λmsubscript𝜆1…subscript𝜆𝑚\\lambda\_{1},\\ldots,\\lambda\_{m} (counted with multiplicity). Then for 0≤p<∞0𝑝0\\leq p<\\infty, we have\
\
|     |     |     |\
| --- | --- | --- |\
|     | ∑i\=1m\|λi\|p≤tr​(\|A\|p).superscriptsubscript𝑖1𝑚superscriptsubscript𝜆𝑖𝑝trsuperscript𝐴𝑝\\sum\_{i=1}^{m}\|\\lambda\_{i}\|^{p}\\leq\\mathrm{tr}(\|A\|^{p}). |     |\
\
###### Proof.\
\
For a positive-semidefinite matrix H𝐻H, the notions of singular value and eigenvalue coincide. Furthermore, we have sj​(Hp)\=sj​(H)psubscript𝑠𝑗superscript𝐻𝑝subscript𝑠𝑗superscript𝐻𝑝s\_{j}(H^{p})=s\_{j}(H)^{p} for all 0<p<∞0𝑝0<p<\\infty. Thus tr​(|A|p)\=∑i\=1msi​(|A|p)\=∑i\=1msi​(A)ptrsuperscript𝐴𝑝superscriptsubscript𝑖1𝑚subscript𝑠𝑖superscript𝐴𝑝superscriptsubscript𝑖1𝑚subscript𝑠𝑖superscript𝐴𝑝\\mathrm{tr}(|A|^{p})=\\sum\_{i=1}^{m}s\_{i}(|A|^{p})=\\sum\_{i=1}^{m}s\_{i}(A)^{p}. The assertion follows from Weyl’s majorant theorem (see \[[1](https://ar5iv.labs.arxiv.org/html/2303.01252#bib.bib1)\
, Theorem II.3.6\]). ∎\
\
###### Proposition 2.6.\
\
*   (i)\
    \
    (Generalized Hölder’s inequality) Let A1,A2,…,Ak∈Mm​(ℂ)subscript𝐴1subscript𝐴2…subscript𝐴𝑘subscript𝑀𝑚ℂA\_{1},A\_{2},\\ldots,A\_{k}\\in M\_{m}(\\mathbb{C}), and r,p1,⋯,pk∈(0,∞)𝑟subscript𝑝1⋯subscript𝑝𝑘0r,p\_{1},\\cdots,p\_{k}\\in(0,\\infty) be such that ∑i\=1k1pi\=1rsuperscriptsubscript𝑖1𝑘1subscript𝑝𝑖1𝑟\\sum\_{i=1}^{k}\\frac{1}{p\_{i}}=\\frac{1}{r}. Then\
    \
    |     |     |     |\
    | --- | --- | --- |\
    |     | tr​(\|∏i\=1kAi\|r)1r≤∏i\=1ktr​(\|Ai\|pi)1pi.trsuperscriptsuperscriptsuperscriptsubscriptproduct𝑖1𝑘subscript𝐴𝑖𝑟1𝑟superscriptsubscriptproduct𝑖1𝑘trsuperscriptsuperscriptsubscript𝐴𝑖subscript𝑝𝑖1subscript𝑝𝑖\\mathrm{tr}\\big{(}\|\\prod\_{i=1}^{k}A\_{i}\|^{r}\\big{)}^{\\frac{1}{r}}\\leq\\prod\_{i=1}^{k}\\mathrm{tr}\\big{(}\|A\_{i}\|^{p\_{i}}\\big{)}^{\\frac{1}{p\_{i}}}. |     |\
    \
*   (ii)\
    \
    Let A,B,C∈Mm​(ℂ)𝐴𝐵𝐶subscript𝑀𝑚ℂA,B,C\\in M\_{m}(\\mathbb{C}). For every p∈(0,∞)𝑝0p\\in(0,\\infty), we have\
    \
    |     |     |     |\
    | --- | --- | --- |\
    |     | tr(\|ABC\|p)≤∥A∥p∥C∥ptr((\|B\|p)\\mathrm{tr}(\|ABC\|^{p})\\leq\\\|A\\\|^{p}\\\|C\\\|^{p}\\mathrm{tr}((\|B\|^{p}) |     |\
    \
\
###### Proof.\
\
Let A,B∈Mm​(ℂ)𝐴𝐵subscript𝑀𝑚ℂA,B\\in M\_{m}(\\mathbb{C}). From (\[[1](https://ar5iv.labs.arxiv.org/html/2303.01252#bib.bib1)\
, (III.19)\]), we have the following majorization inequality,\
\
|     |     |     |\
| --- | --- | --- |\
|     | (log⁡s1​(A​B),…,log⁡sm​(A​B))≺(log⁡(s1​(A)​s1​(B)),…,log⁡(sm​(A)​sm​(B))).precedessubscript𝑠1𝐴𝐵…subscript𝑠𝑚𝐴𝐵subscript𝑠1𝐴subscript𝑠1𝐵…subscript𝑠𝑚𝐴subscript𝑠𝑚𝐵\\Big{(}\\log s\_{1}(AB),\\ldots,\\log s\_{m}(AB)\\Big{)}\\prec\\Big{(}\\log\\big{(}s\_{1}(A)s\_{1}(B)\\big{)},\\ldots,\\log\\big{(}s\_{m}(A)s\_{m}(B)\\big{)}\\Big{)}. |     |\
\
From \[[1](https://ar5iv.labs.arxiv.org/html/2303.01252#bib.bib1)\
, Example II.3.5 (v)\], for every φ:\[0,∞)→ℝ:𝜑→0ℝ\\varphi:\[0,\\infty)\\to\\mathbb{R} such that φ​(et)𝜑superscript𝑒𝑡\\varphi(e^{t}) is convex and monotone increasing in t𝑡t, we have\
\
|     |     |     |     |\
| --- | --- | --- | --- |\
| (2.1) |     | ∑i\=1mφ​(si​(A​B))≤∑i\=1mφ​(si​(A)​si​(B)).superscriptsubscript𝑖1𝑚𝜑subscript𝑠𝑖𝐴𝐵superscriptsubscript𝑖1𝑚𝜑subscript𝑠𝑖𝐴subscript𝑠𝑖𝐵\\sum\_{i=1}^{m}\\varphi\\big{(}s\_{i}(AB)\\big{)}\\leq\\sum\_{i=1}^{m}\\varphi\\big{(}s\_{i}(A)s\_{i}(B)\\big{)}. |     |\
\
(i) We prove the result for k\=2𝑘2k=2. The general case follows from a standard induction argument. Let p,q,r∈(0,∞)𝑝𝑞𝑟0p,q,r\\in(0,\\infty) be such that 1p+1q\=1r1𝑝1𝑞1𝑟\\frac{1}{p}+\\frac{1}{q}=\\frac{1}{r}. Using inequality ([2.1](https://ar5iv.labs.arxiv.org/html/2303.01252#S2.E1 "In Proof. ‣ 2.2. Singular values of matrices ‣ 2. Preparatory results ‣ A stronger form of Yamamoto’s theorem on singular values")\
) for the function t↦trmaps-to𝑡superscript𝑡𝑟t\\mapsto t^{r}, we have\
\
|     |     |     |     |\
| --- | --- | --- | --- |\
|     | tr​(\|A​B\|r)\=∑i\=1msi​(A​B)rtrsuperscript𝐴𝐵𝑟superscriptsubscript𝑖1𝑚subscript𝑠𝑖superscript𝐴𝐵𝑟\\displaystyle\\mathrm{tr}(\|AB\|^{r})=\\sum\_{i=1}^{m}s\_{i}(AB)^{r} | ≤∑i\=1msi​(A)r​si​(B)rabsentsuperscriptsubscript𝑖1𝑚subscript𝑠𝑖superscript𝐴𝑟subscript𝑠𝑖superscript𝐵𝑟\\displaystyle\\leq\\sum\_{i=1}^{m}s\_{i}(A)^{r}s\_{i}(B)^{r} |     |\
|     |     | ≤(∑i\=1msi​(A)p)rp​(∑i\=1msi​(B)q)rqabsentsuperscriptsuperscriptsubscript𝑖1𝑚subscript𝑠𝑖superscript𝐴𝑝𝑟𝑝superscriptsuperscriptsubscript𝑖1𝑚subscript𝑠𝑖superscript𝐵𝑞𝑟𝑞\\displaystyle\\leq\\big{(}\\sum\_{i=1}^{m}s\_{i}(A)^{p})^{\\frac{r}{p}}\\big{(}\\sum\_{i=1}^{m}s\_{i}(B)^{q})^{\\frac{r}{q}} |     |\
|     |     | \=(tr​(\|A\|p))rp​(tr​(\|B\|q))rq,absentsuperscripttrsuperscript𝐴𝑝𝑟𝑝superscripttrsuperscript𝐵𝑞𝑟𝑞\\displaystyle=\\big{(}\\mathrm{tr}(\|A\|^{p})\\big{)}^{\\frac{r}{p}}\\big{(}\\mathrm{tr}(\|B\|^{q})\\big{)}^{\\frac{r}{q}}, |     |\
\
where the second inequality follows from Hölder’s inequality for non-negative real numbers.\
\
(ii) As in part (i), for any two matrices A,B∈Mm​(ℂ)𝐴𝐵subscript𝑀𝑚ℂA,B\\in M\_{m}(\\mathbb{C}) and p∈(0,∞)𝑝0p\\in(0,\\infty), we have\
\
|     |     |     |     |\
| --- | --- | --- | --- |\
|     | tr​(\|A​B\|p)≤∑i\=1msi​(A)p​si​(B)ptrsuperscript𝐴𝐵𝑝superscriptsubscript𝑖1𝑚subscript𝑠𝑖superscript𝐴𝑝subscript𝑠𝑖superscript𝐵𝑝\\displaystyle\\mathrm{tr}(\|AB\|^{p})\\leq\\sum\_{i=1}^{m}s\_{i}(A)^{p}s\_{i}(B)^{p} | ≤∑i\=1ms1​(A)p​si​(B)pabsentsuperscriptsubscript𝑖1𝑚subscript𝑠1superscript𝐴𝑝subscript𝑠𝑖superscript𝐵𝑝\\displaystyle\\leq\\sum\_{i=1}^{m}s\_{1}(A)^{p}s\_{i}(B)^{p} |     |\
|     |     | \=‖A‖p​(∑i\=1msi​(B)p)\=‖A‖p​tr​(\|B\|p).absentsuperscriptnorm𝐴𝑝superscriptsubscript𝑖1𝑚subscript𝑠𝑖superscript𝐵𝑝superscriptnorm𝐴𝑝trsuperscript𝐵𝑝\\displaystyle=\\\|A\\\|^{p}\\big{(}\\sum\_{i=1}^{m}s\_{i}(B)^{p}\\big{)}=\\\|A\\\|^{p}\\mathrm{tr}(\|B\|^{p}). |     |\
\
Similarly tr​(|B​A|p)≤‖A‖p​tr​(|B|p)trsuperscript𝐵𝐴𝑝superscriptnorm𝐴𝑝trsuperscript𝐵𝑝\\mathrm{tr}(|BA|^{p})\\leq\\|A\\|^{p}\\mathrm{tr}(|B|^{p}). Thus\
\
|     |     |     |\
| --- | --- | --- |\
|     | tr​(\|A​B​C\|p)≤‖A‖p​tr​(\|B​C\|p)≤‖A‖p​‖C‖p​tr​(\|B\|p).trsuperscript𝐴𝐵𝐶𝑝superscriptnorm𝐴𝑝trsuperscript𝐵𝐶𝑝superscriptnorm𝐴𝑝superscriptnorm𝐶𝑝trsuperscript𝐵𝑝\\mathrm{tr}(\|ABC\|^{p})\\leq\\\|A\\\|^{p}\\mathrm{tr}(\|BC\|^{p})\\leq\\\|A\\\|^{p}\\\|C\\\|^{p}\\mathrm{tr}(\|B\|^{p}). |     |\
\
∎\
\
###### Corollary 2.7.\
\
Let A𝐴A be a matrix in Mm​(ℂ)subscript𝑀𝑚ℂM\_{m}(\\mathbb{C}). For all n∈ℕ𝑛ℕn\\in\\mathbb{N} and p∈(0,∞)𝑝0p\\in(0,\\infty), we have\
\
|     |     |     |\
| --- | --- | --- |\
|     | tr​(\|An\|pn)≤tr​(\|A\|p).trsuperscriptsuperscript𝐴𝑛𝑝𝑛trsuperscript𝐴𝑝\\mathrm{tr}(\|A^{n}\|^{\\frac{p}{n}})\\leq\\mathrm{tr}(\|A\|^{p}). |     |\
\
###### Proof.\
\
In Proposition [2.6](https://ar5iv.labs.arxiv.org/html/2303.01252#S2.Thmthm6 "Proposition 2.6. ‣ 2.2. Singular values of matrices ‣ 2. Preparatory results ‣ A stronger form of Yamamoto’s theorem on singular values")\
, set A1\=⋯\=An\=Asubscript𝐴1⋯subscript𝐴𝑛𝐴A\_{1}=\\cdots=A\_{n}=A, p1\=⋯\=pn\=psubscript𝑝1⋯subscript𝑝𝑛𝑝p\_{1}=\\cdots=p\_{n}=p and r\=pn𝑟𝑝𝑛r=\\frac{p}{n}. ∎\
\
###### Lemma 2.8.\
\
Let A𝐴A be a matrix in Mm​(ℂ)subscript𝑀𝑚ℂM\_{m}(\\mathbb{C}) and α∈\[0,1\]𝛼01\\alpha\\in\[0,1\]. For every unit vector x→∈ℂm→𝑥superscriptℂ𝑚\\vec{x}\\in\\mathbb{C}^{m} and a positive integer n𝑛n, we have\
\
|     |     |     |\
| --- | --- | --- |\
|     | ‖\|An\|α​x→‖≤‖An​x→‖α.normsuperscriptsuperscript𝐴𝑛𝛼→𝑥superscriptnormsuperscript𝐴𝑛→𝑥𝛼\\\|A^{n}\|^{\\alpha}\\vec{x}\\\|\\leq\\\|A^{n}\\vec{x}\\\|^{\\alpha}. |     |\
\
###### Proof.\
\
Let α∈\[0,1\]𝛼01\\alpha\\in\[0,1\] and H𝐻H be a positive-semidefinite matrix in Mm​(ℂ)subscript𝑀𝑚ℂM\_{m}(\\mathbb{C}). Since U∗​Hα​U\=(U∗​H​U)αsuperscript𝑈superscript𝐻𝛼𝑈superscriptsuperscript𝑈𝐻𝑈𝛼U^{\*}H^{\\alpha}U=(U^{\*}HU)^{\\alpha} for every unitary matrix U∈Mm​(ℂ)𝑈subscript𝑀𝑚ℂU\\in M\_{m}(\\mathbb{C}), without loss of generality, we may assume that H\=diag​(h1,…,hm)𝐻diagsubscriptℎ1…subscriptℎ𝑚H=\\mathrm{diag}(h\_{1},\\ldots,h\_{m}) is in diagonal form. Let x→\=(x1,…,xm)†→𝑥superscriptsubscript𝑥1…subscript𝑥𝑚†\\vec{x}=(x\_{1},\\ldots,x\_{m})^{\\dagger} be a unit vector in ℂmsuperscriptℂ𝑚\\mathbb{C}^{m} so that ∑i\=1m|xi|2\=1superscriptsubscript𝑖1𝑚superscriptsubscript𝑥𝑖21\\sum\_{i=1}^{m}|x\_{i}|^{2}=1. Since, for n∈ℕ𝑛ℕn\\in\\mathbb{N}, the function x↦xαmaps-to𝑥superscript𝑥𝛼x\\mapsto x^{\\alpha} on \[0,∞)0\[0,\\infty) is concave, from Jensen’s inequality for h1,h2,…,hmsubscriptℎ1subscriptℎ2…subscriptℎ𝑚h\_{1},h\_{2},\\ldots,h\_{m} with weights |x1|2,…,|xm|2superscriptsubscript𝑥12…superscriptsubscript𝑥𝑚2|x\_{1}|^{2},\\ldots,|x\_{m}|^{2}, we see that\
\
|     |     |     |\
| --- | --- | --- |\
|     | ⟨Hα​x→,x→⟩\=∑i\=1m\|xi\|2​hiα≤(∑i\=1m\|xi\|2​hi)α\=⟨H​x→,x→⟩α.superscript𝐻𝛼→𝑥→𝑥superscriptsubscript𝑖1𝑚superscriptsubscript𝑥𝑖2superscriptsubscriptℎ𝑖𝛼superscriptsuperscriptsubscript𝑖1𝑚superscriptsubscript𝑥𝑖2subscriptℎ𝑖𝛼superscript𝐻→𝑥→𝑥𝛼\\langle H^{\\alpha}\\vec{x},\\vec{x}\\rangle=\\sum\_{i=1}^{m}\|x\_{i}\|^{2}h\_{i}^{\\alpha}\\leq\\big{(}\\sum\_{i=1}^{m}\|x\_{i}\|^{2}h\_{i}\\big{)}^{\\alpha}=\\langle H\\vec{x},\\vec{x}\\rangle^{\\alpha}. |     |\
\
Using the above inequality for H2superscript𝐻2H^{2}, we get\
\
|     |     |     |\
| --- | --- | --- |\
|     | ‖Hα​x→‖2\=⟨H2​α​x→,x→⟩≤⟨H2​x→,x→⟩α\=‖H​x→‖2​αsuperscriptnormsuperscript𝐻𝛼→𝑥2superscript𝐻2𝛼→𝑥→𝑥superscriptsuperscript𝐻2→𝑥→𝑥𝛼superscriptnorm𝐻→𝑥2𝛼\\\|H^{\\alpha}\\vec{x}\\\|^{2}=\\langle H^{2\\alpha}\\vec{x},\\vec{x}\\rangle\\leq\\langle H^{2}\\vec{x},\\vec{x}\\rangle^{\\alpha}=\\\|H\\vec{x}\\\|^{2\\alpha} |     |\
\
which implies that\
\
|     |     |     |     |\
| --- | --- | --- | --- |\
| (2.2) |     | ‖Hα​x→‖≤‖H​x→‖α.normsuperscript𝐻𝛼→𝑥superscriptnorm𝐻→𝑥𝛼\\\|H^{\\alpha}\\vec{x}\\\|\\leq\\\|H\\vec{x}\\\|^{\\alpha}. |     |\
\
For T∈Mm​(ℂ)𝑇subscript𝑀𝑚ℂT\\in M\_{m}(\\mathbb{C}) and x→∈ℂm→𝑥superscriptℂ𝑚\\vec{x}\\in\\mathbb{C}^{m}, note that\
\
|     |     |     |\
| --- | --- | --- |\
|     | ‖T​x→‖2\=⟨T∗​T​x→,x→⟩\=⟨\|T\|2​x→,x→⟩\=‖\|T\|​x→‖2,superscriptnorm𝑇→𝑥2superscript𝑇𝑇→𝑥→𝑥superscript𝑇2→𝑥→𝑥superscriptnorm𝑇→𝑥2\\\|T\\vec{x}\\\|^{2}=\\langle T^{\*}T\\vec{x},\\vec{x}\\rangle=\\langle\|T\|^{2}\\vec{x},\\vec{x}\\rangle=\\big{\\\|}\|T\|\\vec{x}\\big{\\\|}^{2}, |     |\
\
which implies that ‖T​x→‖\=‖|T|​x→‖norm𝑇→𝑥norm𝑇→𝑥\\|T\\vec{x}\\|=\\big{\\|}|T|\\vec{x}\\big{\\|}. We get the desired inequality by plugging in H\=|An|𝐻superscript𝐴𝑛H=|A^{n}| in inequality ([2.2](https://ar5iv.labs.arxiv.org/html/2303.01252#S2.E2 "In Proof. ‣ 2.2. Singular values of matrices ‣ 2. Preparatory results ‣ A stronger form of Yamamoto’s theorem on singular values")\
). ∎\
\
3\. The Main Theorem\
--------------------\
\
###### Lemma 3.1.\
\
Let A∈Mm​(ℂ)𝐴subscript𝑀𝑚ℂA\\in M\_{m}(\\mathbb{C}) with eigenvalues λ1,…,λmsubscript𝜆1…subscript𝜆𝑚\\lambda\_{1},\\ldots,\\lambda\_{m} (counted with multiplicity). Then there is a sequence of invertible matrices Wn∈G​Ln​(ℂ)subscript𝑊𝑛𝐺subscript𝐿𝑛ℂW\_{n}\\in GL\_{n}(\\mathbb{C}) such that Wn​A​Wn−1→diag​(λ1,…,λn)→subscript𝑊𝑛𝐴superscriptsubscript𝑊𝑛1diagsubscript𝜆1…subscript𝜆𝑛W\_{n}AW\_{n}^{-1}\\to\\mathrm{diag}(\\lambda\_{1},\\ldots,\\lambda\_{n}).\
\
###### Proof.\
\
Without loss of generality, we may assume that A𝐴A is in upper triangular form (by conjugating with an appropriate unitary). For n∈ℕ𝑛ℕn\\in\\mathbb{N}, we define Wn:=diag​(1,n,n2,…,nm−1)assignsubscript𝑊𝑛diag1𝑛superscript𝑛2…superscript𝑛𝑚1W\_{n}:=\\mathrm{diag}(1,n,n^{2},\\ldots,n^{m-1}). A straightforward computation shows that the (i,j)thsuperscript𝑖𝑗th(i,j)^{\\mathrm{th}} entry of Wn​A​Wn−1subscript𝑊𝑛𝐴superscriptsubscript𝑊𝑛1W\_{n}AW\_{n}^{-1} is 1nj−i1superscript𝑛𝑗𝑖\\frac{1}{n^{j-i}} times the (i,j)thsuperscript𝑖𝑗th(i,j)^{\\mathrm{th}} entry of A𝐴A so that the diagonal entries remain unchanged, the superdiagonal entries tend to 00 as n→∞→𝑛n\\to\\infty and the subdiagonal entries remain equal to zero. ∎\
\
###### Proposition 3.2.\
\
Let A∈Mm​(ℂ)𝐴subscript𝑀𝑚ℂA\\in M\_{m}(\\mathbb{C}) with eigenvalues λ1,…,λmsubscript𝜆1…subscript𝜆𝑚\\lambda\_{1},\\ldots,\\lambda\_{m} (counted with multiplicity). Then for 0≤p<∞0𝑝0\\leq p<\\infty, we have\
\
|     |     |     |\
| --- | --- | --- |\
|     | ∑i\=1m\|λi\|p\=limn→∞tr​(\|An\|pn).superscriptsubscript𝑖1𝑚superscriptsubscript𝜆𝑖𝑝subscript→𝑛trsuperscriptsuperscript𝐴𝑛𝑝𝑛\\sum\_{i=1}^{m}\|\\lambda\_{i}\|^{p}=\\lim\_{n\\to\\infty}\\mathrm{tr}(\|A^{n}\|^{\\frac{p}{n}}). |     |\
\
###### Proof.\
\
From Proposition [2.5](https://ar5iv.labs.arxiv.org/html/2303.01252#S2.Thmthm5 "Proposition 2.5. ‣ 2.2. Singular values of matrices ‣ 2. Preparatory results ‣ A stronger form of Yamamoto’s theorem on singular values")\
 and the spectral mapping theorem, for all n∈ℕ𝑛ℕn\\in\\mathbb{N} we have\
\
|     |     |     |\
| --- | --- | --- |\
|     | ∑i\=1m\|λi\|p≤tr​(\|An\|pn).superscriptsubscript𝑖1𝑚superscriptsubscript𝜆𝑖𝑝trsuperscriptsuperscript𝐴𝑛𝑝𝑛\\sum\_{i=1}^{m}\|\\lambda\_{i}\|^{p}\\leq\\mathrm{tr}(\|A^{n}\|^{\\frac{p}{n}}). |     |\
\
Thus\
\
|     |     |     |     |\
| --- | --- | --- | --- |\
| (3.1) |     | ∑i\=1m\|λi\|p≤lim infn→∞tr​(\|An\|pn).superscriptsubscript𝑖1𝑚superscriptsubscript𝜆𝑖𝑝subscriptlimit-infimum→𝑛trsuperscriptsuperscript𝐴𝑛𝑝𝑛\\sum\_{i=1}^{m}\|\\lambda\_{i}\|^{p}\\leq\\liminf\_{n\\to\\infty}\\mathrm{tr}(\|A^{n}\|^{\\frac{p}{n}}). |     |\
\
Let Wnsubscript𝑊𝑛W\_{n} be as defined in the proof of Lemma [3.1](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.Thmthm1 "Lemma 3.1. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
.. For n∈ℕ𝑛ℕn\\in\\mathbb{N}, define Λn:=Wn​A​Wn−1assignsubscriptΛ𝑛subscript𝑊𝑛𝐴superscriptsubscript𝑊𝑛1\\Lambda\_{n}:=W\_{n}AW\_{n}^{-1}. From Proposition [2.5](https://ar5iv.labs.arxiv.org/html/2303.01252#S2.Thmthm5 "Proposition 2.5. ‣ 2.2. Singular values of matrices ‣ 2. Preparatory results ‣ A stronger form of Yamamoto’s theorem on singular values")\
, we have\
\
|     |     |     |\
| --- | --- | --- |\
|     | tr​(\|Λn\|p)≥∑i\=1m\|λi\|p,∀n∈ℕ.formulae-sequencetrsuperscriptsubscriptΛ𝑛𝑝superscriptsubscript𝑖1𝑚superscriptsubscript𝜆𝑖𝑝for-all𝑛ℕ\\mathrm{tr}(\|\\Lambda\_{n}\|^{p})\\geq\\sum\_{i=1}^{m}\|\\lambda\_{i}\|^{p},\\;\\;\\;\\forall n\\in\\mathbb{N}. |     |\
\
Since |Λn|p→diag​(|λ1|p,…,|λm|p)→superscriptsubscriptΛ𝑛𝑝diagsuperscriptsubscript𝜆1𝑝…superscriptsubscript𝜆𝑚𝑝|\\Lambda\_{n}|^{p}\\to\\mathrm{diag}(|\\lambda\_{1}|^{p},\\ldots,|\\lambda\_{m}|^{p}) as n→∞→𝑛n\\to\\infty, we observe that\
\
|     |     |     |\
| --- | --- | --- |\
|     | limn→∞tr​(\|Λn\|p)\=∑i\=1m\|λi\|p.subscript→𝑛trsuperscriptsubscriptΛ𝑛𝑝superscriptsubscript𝑖1𝑚superscriptsubscript𝜆𝑖𝑝\\lim\_{n\\to\\infty}\\mathrm{tr}(\|\\Lambda\_{n}\|^{p})=\\sum\_{i=1}^{m}\|\\lambda\_{i}\|^{p}. |     |\
\
Let ε\>0𝜀0\\varepsilon>0. Then there exist k∈ℕ𝑘ℕk\\in\\mathbb{N} such that tr​(|Λk|p)≤∑i\=1m|λi|p+εtrsuperscriptsubscriptΛ𝑘𝑝superscriptsubscript𝑖1𝑚superscriptsubscript𝜆𝑖𝑝𝜀\\mathrm{tr}(|\\Lambda\_{k}|^{p})\\leq\\sum\_{i=1}^{m}|\\lambda\_{i}|^{p}+\\varepsilon. From Corollary [2.7](https://ar5iv.labs.arxiv.org/html/2303.01252#S2.Thmthm7 "Corollary 2.7. ‣ 2.2. Singular values of matrices ‣ 2. Preparatory results ‣ A stronger form of Yamamoto’s theorem on singular values")\
, we see that\
\
|     |     |     |\
| --- | --- | --- |\
|     | tr​(\|Λkn\|pn)≤tr​(\|Λk\|p)≤∑i\=1m\|λi\|p+ε.trsuperscriptsuperscriptsubscriptΛ𝑘𝑛𝑝𝑛trsuperscriptsubscriptΛ𝑘𝑝superscriptsubscript𝑖1𝑚superscriptsubscript𝜆𝑖𝑝𝜀\\mathrm{tr}(\|\\Lambda\_{k}^{n}\|^{\\frac{p}{n}})\\leq\\mathrm{tr}(\|\\Lambda\_{k}\|^{p})\\leq\\sum\_{i=1}^{m}\|\\lambda\_{i}\|^{p}+\\varepsilon. |     |\
\
Since An\=Wk−1​Λkn​Wksuperscript𝐴𝑛superscriptsubscript𝑊𝑘1superscriptsubscriptΛ𝑘𝑛subscript𝑊𝑘A^{n}=W\_{k}^{-1}\\Lambda\_{k}^{n}W\_{k}, from Proposition [2.6](https://ar5iv.labs.arxiv.org/html/2303.01252#S2.Thmthm6 "Proposition 2.6. ‣ 2.2. Singular values of matrices ‣ 2. Preparatory results ‣ A stronger form of Yamamoto’s theorem on singular values")\
\-(ii), it follows that\
\
|     |     |     |     |\
| --- | --- | --- | --- |\
|     | tr​(\|An\|pn)\=tr​(\|Wk−1​Λkn​Wk\|pn)trsuperscriptsuperscript𝐴𝑛𝑝𝑛trsuperscriptsuperscriptsubscript𝑊𝑘1superscriptsubscriptΛ𝑘𝑛subscript𝑊𝑘𝑝𝑛\\displaystyle\\mathrm{tr}(\|A^{n}\|^{\\frac{p}{n}})=\\mathrm{tr}(\|W\_{k}^{-1}\\Lambda\_{k}^{n}W\_{k}\|^{\\frac{p}{n}}) | ≤‖Wk−1‖pn​‖Wk‖pn​tr​(\|Λkn\|pn)absentsuperscriptnormsuperscriptsubscript𝑊𝑘1𝑝𝑛superscriptnormsubscript𝑊𝑘𝑝𝑛trsuperscriptsuperscriptsubscriptΛ𝑘𝑛𝑝𝑛\\displaystyle\\leq\\\|W\_{k}^{-1}\\\|^{\\frac{p}{n}}\\\|W\_{k}\\\|^{\\frac{p}{n}}\\;\\mathrm{tr}(\|\\Lambda\_{k}^{n}\|^{\\frac{p}{n}}) |     |\
|     |     | ≤(∥Wk−1∥∥Wk∥)pn)(∑i\=1m\|λi\|p+ε).\\displaystyle\\leq(\\\|W\_{k}^{-1}\\\|\\\|W\_{k}\\\|)^{\\frac{p}{n}})\\Big{(}\\sum\_{i=1}^{m}\|\\lambda\_{i}\|^{p}+\\varepsilon\\Big{)}. |     |\
\
Thus for all ε\>0𝜀0\\varepsilon>0, we have\
\
|     |     |     |\
| --- | --- | --- |\
|     | lim supn→∞tr​(\|An\|pn)≤∑i\=1m\|λi\|p+ε,subscriptlimit-supremum→𝑛trsuperscriptsuperscript𝐴𝑛𝑝𝑛superscriptsubscript𝑖1𝑚superscriptsubscript𝜆𝑖𝑝𝜀\\limsup\_{n\\to\\infty}\\mathrm{tr}(\|A^{n}\|^{\\frac{p}{n}})\\leq\\sum\_{i=1}^{m}\|\\lambda\_{i}\|^{p}+\\varepsilon, |     |\
\
which implies that\
\
|     |     |     |     |\
| --- | --- | --- | --- |\
| (3.2) |     | lim supn→∞tr​(\|An\|pn)≤∑i\=1m\|λi\|p.subscriptlimit-supremum→𝑛trsuperscriptsuperscript𝐴𝑛𝑝𝑛superscriptsubscript𝑖1𝑚superscriptsubscript𝜆𝑖𝑝\\limsup\_{n\\to\\infty}\\mathrm{tr}(\|A^{n}\|^{\\frac{p}{n}})\\leq\\sum\_{i=1}^{m}\|\\lambda\_{i}\|^{p}. |     |\
\
Combining the inequalities ([3.1](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.E1 "In Proof. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
) and ([3.2](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.E2 "In Proof. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
), we get the desired result. ∎\
\
###### Proposition 3.3.\
\
Let A𝐴A be a matrix in Mm​(ℂ)subscript𝑀𝑚ℂM\_{m}(\\mathbb{C}).\
\
*   (i)\
    \
    The set of limit points of the sequence {|An|1n}n∈ℕsubscriptsuperscriptsuperscript𝐴𝑛1𝑛𝑛ℕ\\{|A^{n}|^{\\frac{1}{n}}\\}\_{n\\in\\mathbb{N}} is non-empty and consists of positive-semidefinite matrices.\
    \
\
Let H𝐻H be a limit point of the sequence {|An|1n}n∈ℕsubscriptsuperscriptsuperscript𝐴𝑛1𝑛𝑛ℕ\\{|A^{n}|^{\\frac{1}{n}}\\}\_{n\\in\\mathbb{N}}.\
\
*   (ii)\
    \
    For every p∈(0,∞)𝑝0p\\in(0,\\infty), we have tr​(Hp)\=∑i\=1n|λi|ptrsuperscript𝐻𝑝superscriptsubscript𝑖1𝑛superscriptsubscript𝜆𝑖𝑝\\mathrm{tr}(H^{p})=\\sum\_{i=1}^{n}|\\lambda\_{i}|^{p}.\
    \
*   (iii)\
    \
    |λ|​(H)\=|λ|​(A)𝜆𝐻𝜆𝐴|\\lambda|(H)=|\\lambda|(A).\
    \
\
###### Proof.\
\
(i) Let A∈Mm​(ℂ)𝐴subscript𝑀𝑚ℂA\\in M\_{m}(\\mathbb{C}). Note that ‖|An|1n‖\=‖|An|‖1n\=‖An‖1n≤‖A‖normsuperscriptsuperscript𝐴𝑛1𝑛superscriptnormsuperscript𝐴𝑛1𝑛superscriptnormsuperscript𝐴𝑛1𝑛norm𝐴\\||A^{n}|^{\\frac{1}{n}}\\|=\\||A^{n}|\\|^{\\frac{1}{n}}=\\|A^{n}\\|^{\\frac{1}{n}}\\leq\\|A\\| for all n∈ℕ𝑛ℕn\\in\\mathbb{N}. Since the ball of radius ‖A‖norm𝐴\\|A\\| in Mm​(ℂ)subscript𝑀𝑚ℂM\_{m}(\\mathbb{C}) is compact, the set of limit-points of the sequence {|An|1n}n∈ℕsubscriptsuperscriptsuperscript𝐴𝑛1𝑛𝑛ℕ\\{|A^{n}|^{\\frac{1}{n}}\\}\_{n\\in\\mathbb{N}} is non-empty. Positivity of the limit-points follows from the fact that the cone of positive-semidefinite matrices is norm-closed.\
\
(ii) Let {|Ank|1nk}superscriptsuperscript𝐴subscript𝑛𝑘1subscript𝑛𝑘\\{|A^{n\_{k}}|^{\\frac{1}{n\_{k}}}\\} be a subsequence of {|An|1n}superscriptsuperscript𝐴𝑛1𝑛\\{|A^{n}|^{\\frac{1}{n}}\\} converging to H𝐻H. Then for all p∈(0,∞)𝑝0p\\in(0,\\infty), we have |Ank|pnk→Hp→superscriptsuperscript𝐴subscript𝑛𝑘𝑝subscript𝑛𝑘superscript𝐻𝑝|A^{n\_{k}}|^{\\frac{p}{n\_{k}}}\\to H^{p} so that tr​(|Ank|pnk)→tr​(Hp)→trsuperscriptsuperscript𝐴subscript𝑛𝑘𝑝subscript𝑛𝑘trsuperscript𝐻𝑝\\mathrm{tr}(|A^{n\_{k}}|^{\\frac{p}{n\_{k}}})\\to\\mathrm{tr}(H^{p}). Let λ1,…,λmsubscript𝜆1…subscript𝜆𝑚\\lambda\_{1},\\ldots,\\lambda\_{m} be the eigenvalues of A𝐴A (counted with multiplicity). By Proposition [3.2](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.Thmthm2 "Proposition 3.2. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
, tr​(Hp)\=∑i\=1m|λi|ptrsuperscript𝐻𝑝superscriptsubscript𝑖1𝑚superscriptsubscript𝜆𝑖𝑝\\mathrm{tr}(H^{p})=\\sum\_{i=1}^{m}|\\lambda\_{i}|^{p} for all p∈(0,∞)𝑝0p\\in(0,\\infty).\
\
(iii) Let μ1,…,μmsubscript𝜇1…subscript𝜇𝑚\\mu\_{1},\\ldots,\\mu\_{m} be the eigenvalues of H𝐻H (counted with multiplicity). Since H𝐻H is positive-semidefinite, we have\
\
|     |     |     |\
| --- | --- | --- |\
|     | ∑i\=1mμip\=tr​(Hp)\=∑i\=1m\|λi\|psuperscriptsubscript𝑖1𝑚superscriptsubscript𝜇𝑖𝑝trsuperscript𝐻𝑝superscriptsubscript𝑖1𝑚superscriptsubscript𝜆𝑖𝑝\\sum\_{i=1}^{m}\\mu\_{i}^{p}=\\mathrm{tr}(H^{p})=\\sum\_{i=1}^{m}\|\\lambda\_{i}\|^{p} |     |\
\
for all p∈(0,∞).𝑝0p\\in(0,\\infty). Thus the multisets {μ1,μ2,…,μm}subscript𝜇1subscript𝜇2…subscript𝜇𝑚\\{\\mu\_{1},\\mu\_{2},\\ldots,\\mu\_{m}\\} and {|λ1|,|λ2|,…,|λm|}subscript𝜆1subscript𝜆2…subscript𝜆𝑚\\{|\\lambda\_{1}|,|\\lambda\_{2}|,\\ldots,|\\lambda\_{m}|\\} are identical.\
\
∎\
\
###### Definition 3.4.\
\
Let A𝐴A be a matrix in Mm​(ℂ)subscript𝑀𝑚ℂM\_{m}(\\mathbb{C}). For r≥0𝑟0r\\geq 0, we define\
\
|     |     |     |\
| --- | --- | --- |\
|     | V​(A,r):={x→∈ℂm:lim supn‖An​x→‖1n≤r}.assign𝑉𝐴𝑟conditional-set→𝑥superscriptℂ𝑚subscriptlimit-supremum𝑛superscriptnormsuperscript𝐴𝑛→𝑥1𝑛𝑟V(A,r):=\\{\\vec{x}\\in\\mathbb{C}^{m}:\\limsup\_{n}\\\|A^{n}\\vec{x}\\\|^{\\frac{1}{n}}\\leq r\\}. |     |\
\
###### Lemma 3.5.\
\
Let A𝐴A be a matrix in Mm​(ℂ)subscript𝑀𝑚ℂM\_{m}(\\mathbb{C}). Let A\=D+N𝐴𝐷𝑁A=D+N be the Jordan-Chevalley decomposition of A𝐴A into its (commuting) diagonalizable and nilpotent parts (D,N𝐷𝑁D,N, respectively). For every r≥0𝑟0r\\geq 0, the set V​(A,r)𝑉𝐴𝑟V(A,r) is a linear subspace of ℂmsuperscriptℂ𝑚\\mathbb{C}^{m} and contains the eigenvectors of D𝐷D corresponding to eigenvalues λ𝜆\\lambda with |λ|≤r𝜆𝑟|\\lambda|\\leq r.\
\
###### Proof.\
\
Let x→,y→∈ℂm→𝑥→𝑦superscriptℂ𝑚\\vec{x},\\vec{y}\\in\\mathbb{C}^{m} and μ∈ℂ𝜇ℂ\\mu\\in\\mathbb{C}. By Lemma [2.2](https://ar5iv.labs.arxiv.org/html/2303.01252#S2.Thmthm2 "Lemma 2.2. ‣ 2.1. Some elementary results on sequences of real numbers ‣ 2. Preparatory results ‣ A stronger form of Yamamoto’s theorem on singular values")\
, we have\
\
|     |     |     |     |\
| --- | --- | --- | --- |\
|     | lim supn‖An​(μ​x→+y→)‖1nsubscriptlimit-supremum𝑛superscriptnormsuperscript𝐴𝑛𝜇→𝑥→𝑦1𝑛\\displaystyle\\limsup\_{n}\\\|A^{n}(\\mu\\vec{x}+\\vec{y})\\\|^{\\frac{1}{n}} | ≤lim supn(\|μ\|​‖An​x→‖+‖An​y→‖)1nabsentsubscriptlimit-supremum𝑛superscript𝜇normsuperscript𝐴𝑛→𝑥normsuperscript𝐴𝑛→𝑦1𝑛\\displaystyle\\leq\\limsup\_{n}\\big{(}\|\\mu\|\\\|A^{n}\\vec{x}\\\|+\\\|A^{n}\\vec{y}\\\|\\big{)}^{\\frac{1}{n}} |     |\
|     |     | ≤max⁡{lim supn\|μ\|1n​‖An​x→‖1n,lim supn‖An​y→‖1n}absentsubscriptlimit-supremum𝑛superscript𝜇1𝑛superscriptnormsuperscript𝐴𝑛→𝑥1𝑛subscriptlimit-supremum𝑛superscriptnormsuperscript𝐴𝑛→𝑦1𝑛\\displaystyle\\leq\\max\\big{\\{}\\limsup\_{n}\|\\mu\|^{\\frac{1}{n}}\\\|A^{n}\\vec{x}\\\|^{\\frac{1}{n}},\\limsup\_{n}\\\|A^{n}\\vec{y}\\\|^{\\frac{1}{n}}\\big{\\}} |     |\
|     |     | ≤r.absent𝑟\\displaystyle\\leq r. |     |\
\
Thus μ​x→+y→∈V​(A,r)𝜇→𝑥→𝑦𝑉𝐴𝑟\\mu\\vec{x}+\\vec{y}\\in V(A,r). This shows that V​(A,r)𝑉𝐴𝑟V(A,r) is a linear subspace of ℂmsuperscriptℂ𝑚\\mathbb{C}^{m}.\
\
Let x→→𝑥\\vec{x} be an eigenvector of D𝐷D with eigenvalue λ𝜆\\lambda. Below we show that x→∈V​(A,|λ|)→𝑥𝑉𝐴𝜆\\vec{x}\\in V(A,|\\lambda|) (which completes the proof of the lemma). Since N𝑁N is an m×m𝑚𝑚m\\times m nilpotent matrix, we have Nm\=0superscript𝑁𝑚0N^{m}=0. Since D𝐷D and N𝑁N commute, for n≥m𝑛𝑚n\\geq m we have\
\
|     |     |     |\
| --- | --- | --- |\
|     | An\=(D+N)n\=∑j\=0m−1(nj)​Nj​Dn−j.superscript𝐴𝑛superscript𝐷𝑁𝑛superscriptsubscript𝑗0𝑚1binomial𝑛𝑗superscript𝑁𝑗superscript𝐷𝑛𝑗A^{n}=(D+N)^{n}=\\sum\_{j=0}^{m-1}\\binom{n}{j}N^{j}D^{n-j}. |     |\
\
Thus An​x→\=∑j\=0m−1(nj)​λn−j​Nj​x→.superscript𝐴𝑛→𝑥superscriptsubscript𝑗0𝑚1binomial𝑛𝑗superscript𝜆𝑛𝑗superscript𝑁𝑗→𝑥A^{n}\\vec{x}=\\sum\_{j=0}^{m-1}\\binom{n}{j}\\lambda^{n-j}N^{j}\\vec{x}. From Lemma [2.1](https://ar5iv.labs.arxiv.org/html/2303.01252#S2.Thmthm1 "Lemma 2.1. ‣ 2.1. Some elementary results on sequences of real numbers ‣ 2. Preparatory results ‣ A stronger form of Yamamoto’s theorem on singular values")\
 we have\
\
|     |     |     |\
| --- | --- | --- |\
|     | limn\|λ\|1−jn​(nj)1n​‖Nj​x→‖1n≤\|λ\|, for ​0≤j≤m−1.formulae-sequencesubscript𝑛superscript𝜆1𝑗𝑛superscriptbinomial𝑛𝑗1𝑛superscriptnormsuperscript𝑁𝑗→𝑥1𝑛𝜆 for 0𝑗𝑚1\\lim\_{n}\|\\lambda\|^{1-\\frac{j}{n}}\\binom{n}{j}^{\\frac{1}{n}}\\\|N^{j}\\vec{x}\\\|^{\\frac{1}{n}}\\leq\|\\lambda\|,\\textrm{ for }0\\leq j\\leq m-1. |     |\
\
Using Lemma [2.2](https://ar5iv.labs.arxiv.org/html/2303.01252#S2.Thmthm2 "Lemma 2.2. ‣ 2.1. Some elementary results on sequences of real numbers ‣ 2. Preparatory results ‣ A stronger form of Yamamoto’s theorem on singular values")\
, we conclude that\
\
|     |     |     |     |\
| --- | --- | --- | --- |\
|     | lim supn‖An​x→‖1nsubscriptlimit-supremum𝑛superscriptnormsuperscript𝐴𝑛→𝑥1𝑛\\displaystyle\\limsup\_{n}\\\|A^{n}\\vec{x}\\\|^{\\frac{1}{n}} | ≤lim supn(∑j\=0m−1\|λ\|1−jn​(nj)1n​‖Nj​x→‖1n)absentsubscriptlimit-supremum𝑛superscriptsubscript𝑗0𝑚1superscript𝜆1𝑗𝑛superscriptbinomial𝑛𝑗1𝑛superscriptnormsuperscript𝑁𝑗→𝑥1𝑛\\displaystyle\\leq\\limsup\_{n}\\Big{(}\\sum\_{j=0}^{m-1}\|\\lambda\|^{1-\\frac{j}{n}}\\binom{n}{j}^{\\frac{1}{n}}\\\|N^{j}\\vec{x}\\\|^{\\frac{1}{n}}\\Big{)} |     |\
|     |     | ≤max0≤j≤m−1⁡{limn\|λ\|1−jn​(nj)1n​‖Nj​x→‖1n}absentsubscript0𝑗𝑚1subscript𝑛superscript𝜆1𝑗𝑛superscriptbinomial𝑛𝑗1𝑛superscriptnormsuperscript𝑁𝑗→𝑥1𝑛\\displaystyle\\leq\\max\_{0\\leq j\\leq m-1}\\big{\\{}\\lim\_{n}\|\\lambda\|^{1-\\frac{j}{n}}\\binom{n}{j}^{\\frac{1}{n}}\\\|N^{j}\\vec{x}\\\|^{\\frac{1}{n}}\\big{\\}} |     |\
|     |     | ≤\|λ\|.absent𝜆\\displaystyle\\leq\|\\lambda\|. |     |\
\
Thus x→∈V​(A,|λ|)→𝑥𝑉𝐴𝜆\\vec{x}\\in V(A,|\\lambda|). ∎\
\
###### Lemma 3.6.\
\
Let H𝐻H be a positive-semidefinite matrix with spectral decomposition ∑i\=1kai​Fisuperscriptsubscript𝑖1𝑘subscript𝑎𝑖subscript𝐹𝑖\\sum\_{i=1}^{k}a\_{i}F\_{i}. Set ak+1:=∞assignsubscript𝑎𝑘1a\_{k+1}:=\\infty.\
\
*   (i)\
    \
    For 1≤j≤k1𝑗𝑘1\\leq j\\leq k and r∈\[aj,aj+1)𝑟subscript𝑎𝑗subscript𝑎𝑗1r\\in\[a\_{j},a\_{j+1}), we have V​(H,r)\=V​(H,aj)\=ran​(∑i\=1jFi)𝑉𝐻𝑟𝑉𝐻subscript𝑎𝑗ransuperscriptsubscript𝑖1𝑗subscript𝐹𝑖V(H,r)=V(H,a\_{j})=\\mathrm{ran}\\big{(}\\sum\_{i=1}^{j}F\_{i}\\big{)};\
    \
*   (ii)\
    \
    If H1,H2subscript𝐻1subscript𝐻2H\_{1},H\_{2} are positive-semidefinite matrices in Mm​(ℂ)subscript𝑀𝑚ℂM\_{m}(\\mathbb{C}) such that V​(H1,r)\=V​(H2,r)𝑉subscript𝐻1𝑟𝑉subscript𝐻2𝑟V(H\_{1},r)=V(H\_{2},r) for all r≥0𝑟0r\\geq 0, then H1\=H2subscript𝐻1subscript𝐻2H\_{1}=H\_{2}.\
    \
\
###### Proof.\
\
Let x→→𝑥\\vec{x} be a unit vector in ℂmsuperscriptℂ𝑚\\mathbb{C}^{m}, and define tj:=⟨Fj​x→,x→⟩≥0assignsubscript𝑡𝑗subscript𝐹𝑗→𝑥→𝑥0t\_{j}:=\\langle F\_{j}\\vec{x},\\vec{x}\\rangle\\geq 0. Since ∑i\=1nti\=1superscriptsubscript𝑖1𝑛subscript𝑡𝑖1\\sum\_{i=1}^{n}t\_{i}=1, clearly not all of the tisubscript𝑡𝑖t\_{i}’s are zero. Let 1≤ℓ≤k1ℓ𝑘1\\leq\\ell\\leq k be the largest integer such that tℓ≠0subscript𝑡ℓ0t\_{\\ell}\\neq 0. Note that\
\
|     |     |     |\
| --- | --- | --- |\
|     | ⟨H2​n​x→,x→⟩\=⟨(∑i\=1kai2​n​Fi)​x→,x→⟩\=∑i\=1mai2​n​ti.superscript𝐻2𝑛→𝑥→𝑥superscriptsubscript𝑖1𝑘superscriptsubscript𝑎𝑖2𝑛subscript𝐹𝑖→𝑥→𝑥superscriptsubscript𝑖1𝑚superscriptsubscript𝑎𝑖2𝑛subscript𝑡𝑖\\langle H^{2n}\\vec{x},\\vec{x}\\rangle=\\big{\\langle}(\\sum\_{i=1}^{k}a\_{i}^{2n}F\_{i})\\vec{x},\\vec{x}\\big{\\rangle}=\\sum\_{i=1}^{m}a\_{i}^{2n}t\_{i}. |     |\
\
Using Lemma [2.3](https://ar5iv.labs.arxiv.org/html/2303.01252#S2.Thmthm3 "Lemma 2.3. ‣ 2.1. Some elementary results on sequences of real numbers ‣ 2. Preparatory results ‣ A stronger form of Yamamoto’s theorem on singular values")\
, we have\
\
|     |     |     |\
| --- | --- | --- |\
|     | limn→∞‖Hn​x→‖1n\=limn→∞⟨H2​n​x→,x→⟩12​n\=aℓ.subscript→𝑛superscriptnormsuperscript𝐻𝑛→𝑥1𝑛subscript→𝑛superscriptsuperscript𝐻2𝑛→𝑥→𝑥12𝑛subscript𝑎ℓ\\lim\_{n\\to\\infty}\\\|H^{n}\\vec{x}\\\|^{\\frac{1}{n}}=\\lim\_{n\\to\\infty}\\langle H^{2n}\\vec{x},\\vec{x}\\rangle^{\\frac{1}{2n}}=a\_{\\ell}. |     |\
\
Thus x→∈V​(H,aj)→𝑥𝑉𝐻subscript𝑎𝑗\\vec{x}\\in V(H,a\_{j}) if and only if ∑i\=j+1k⟨Fi​x→,x→⟩\=0superscriptsubscript𝑖𝑗1𝑘subscript𝐹𝑖→𝑥→𝑥0\\sum\_{i=j+1}^{k}\\langle F\_{i}\\vec{x},\\vec{x}\\rangle=0, which holds if and only if x→→𝑥\\vec{x} is in the range of ∑i\=1jFisuperscriptsubscript𝑖1𝑗subscript𝐹𝑖\\sum\_{i=1}^{j}F\_{i}. ∎\
\
###### Proposition 3.7.\
\
Let A be a matrix in Mm​(C)subscript𝑀𝑚𝐶M\_{m}(C). Let A\=D+N𝐴𝐷𝑁A=D+N be the Jordan-Chevalley decomposition of A𝐴A into its commuting diagonalizable and nilpotent parts (D𝐷D, N𝑁N, respectively). Let H𝐻H be a limit point of the sequence {|An|1n}n∈ℕsubscriptsuperscriptsuperscript𝐴𝑛1𝑛𝑛ℕ\\{|A^{n}|^{\\frac{1}{n}}\\}\_{n\\in\\mathbb{N}}. Then for every r≥0𝑟0r\\geq 0, we have V​(A,r)\=V​(H,r)𝑉𝐴𝑟𝑉𝐻𝑟V(A,r)=V(H,r), both of which are equal to the span of the set of eigenvectors of D𝐷D with eigenvalue-modulus less than or equal to r𝑟r.\
\
###### Proof.\
\
Let {a1,a2,…,ak}subscript𝑎1subscript𝑎2…subscript𝑎𝑘\\{a\_{1},a\_{2},\\ldots,a\_{k}\\} be the support of the multiset of modulus of eigenvalues of A𝐴A, with 0≤a1<a2<⋯<ak0subscript𝑎1subscript𝑎2⋯subscript𝑎𝑘0\\leq a\_{1}<a\_{2}<\\cdots<a\_{k}, and ajsubscript𝑎𝑗a\_{j} occurring with multiplicity mjsubscript𝑚𝑗m\_{j}. Note that D𝐷D has the same multiset of eigenvalues as A𝐴A. Since D𝐷D (being diagonalizable) has a complete set of eigenvectors spanning ℂmsuperscriptℂ𝑚\\mathbb{C}^{m}, there are ∑i\=1jmjsuperscriptsubscript𝑖1𝑗subscript𝑚𝑗\\sum\_{i=1}^{j}m\_{j} linearly-independent eigenvectors of D𝐷D with eigenvalue-modulus less than or equal to ajsubscript𝑎𝑗a\_{j}. Let r∈\[aj,aj+1)𝑟subscript𝑎𝑗subscript𝑎𝑗1r\\in\[a\_{j},a\_{j+1}), with the convention ak+1:=∞assignsubscript𝑎𝑘1a\_{k+1}:=\\infty. We observe that\
\
|     |     |     |\
| --- | --- | --- |\
|     | dimV​(H,r)\=dimV​(H,aj)\=∑i\=1jmj≤dimV​(A,aj)dimension𝑉𝐻𝑟dimension𝑉𝐻subscript𝑎𝑗superscriptsubscript𝑖1𝑗subscript𝑚𝑗dimension𝑉𝐴subscript𝑎𝑗\\dim V(H,r)=\\dim V(H,a\_{j})=\\sum\_{i=1}^{j}m\_{j}\\leq\\dim V(A,a\_{j}) |     |\
\
where the first equality follows from Lemma [3.6](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.Thmthm6 "Lemma 3.6. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
\-(i), the second equality follows from Proposition [3.3](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.Thmthm3 "Proposition 3.3. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
\-(iii), and the inequality follows from Lemma [3.5](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.Thmthm5 "Lemma 3.5. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
. Since V​(A,aj)⊆V​(A,r)𝑉𝐴subscript𝑎𝑗𝑉𝐴𝑟V(A,a\_{j})\\subseteq V(A,r), we have\
\
|     |     |     |     |\
| --- | --- | --- | --- |\
| (3.3) |     | dimV​(H,r)\=∑i\=1jmj≤dimV​(A,r).dimension𝑉𝐻𝑟superscriptsubscript𝑖1𝑗subscript𝑚𝑗dimension𝑉𝐴𝑟\\dim V(H,r)=\\sum\_{i=1}^{j}m\_{j}\\leq\\dim V(A,r). |     |\
\
Let the subsequence {|Ank|1nk}superscriptsuperscript𝐴subscript𝑛𝑘1subscript𝑛𝑘\\big{\\{}|A^{n\_{k}}|^{\\frac{1}{n\_{k}}}\\big{\\}} converge to H𝐻H. Then {|Ank|pnk}superscriptsuperscript𝐴subscript𝑛𝑘𝑝subscript𝑛𝑘\\big{\\{}|A^{n\_{k}}|^{\\frac{p}{n\_{k}}}\\big{\\}} converges to Hpsuperscript𝐻𝑝H^{p} for every p∈(0,∞)𝑝0p\\in(0,\\infty). Using Lemma [2.8](https://ar5iv.labs.arxiv.org/html/2303.01252#S2.Thmthm8 "Lemma 2.8. ‣ 2.2. Singular values of matrices ‣ 2. Preparatory results ‣ A stronger form of Yamamoto’s theorem on singular values")\
, for every p∈(0,∞)𝑝0p\\in(0,\\infty), we have\
\
|     |     |     |\
| --- | --- | --- |\
|     | ‖Hp​x→‖\=limnk‖\|Ank\|pnk​x→‖≤lim supnk‖Ank​x→‖pnk≤lim supn‖An​x→‖pn≤rp.normsuperscript𝐻𝑝→𝑥subscriptsubscript𝑛𝑘normsuperscriptsuperscript𝐴subscript𝑛𝑘𝑝subscript𝑛𝑘→𝑥subscriptlimit-supremumsubscript𝑛𝑘superscriptnormsuperscript𝐴subscript𝑛𝑘→𝑥𝑝subscript𝑛𝑘subscriptlimit-supremum𝑛superscriptnormsuperscript𝐴𝑛→𝑥𝑝𝑛superscript𝑟𝑝\\\|H^{p}\\vec{x}\\\|=\\lim\_{n\_{k}}\\big{\\\|}\|A^{n\_{k}}\|^{\\frac{p}{n\_{k}}}\\vec{x}\\big{\\\|}\\leq\\limsup\_{n\_{k}}\\\|A^{n\_{k}}\\vec{x}\\\|^{\\frac{p}{n\_{k}}}\\leq\\limsup\_{n}\\\|A^{n}\\vec{x}\\\|^{\\frac{p}{n}}\\leq r^{p}. |     |\
\
Thus ‖Hp​x→‖1p≤rsuperscriptnormsuperscript𝐻𝑝→𝑥1𝑝𝑟\\|H^{p}\\vec{x}\\|^{\\frac{1}{p}}\\leq r for every p∈(0,∞)𝑝0p\\in(0,\\infty) which implies that x→∈V​(H,r)→𝑥𝑉𝐻𝑟\\vec{x}\\in V(H,r). We conclude that\
\
|     |     |     |     |\
| --- | --- | --- | --- |\
| (3.4) |     | V​(A,r)⊆V​(H,r), for ​1≤j≤k.formulae-sequence𝑉𝐴𝑟𝑉𝐻𝑟 for 1𝑗𝑘V(A,r)\\subseteq V(H,r),\\textrm{ for }1\\leq j\\leq k. |     |\
\
Combining ([3.3](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.E3 "In Proof. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
) and ([3.4](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.E4 "In Proof. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
), we have V​(A,r)\=V​(H,r)𝑉𝐴𝑟𝑉𝐻𝑟V(A,r)=V(H,r) and dimV​(A,r)\=dimV​(H,r)\=∑i\=1jmjdimension𝑉𝐴𝑟dimension𝑉𝐻𝑟superscriptsubscript𝑖1𝑗subscript𝑚𝑗\\dim V(A,r)=\\dim V(H,r)=\\sum\_{i=1}^{j}m\_{j} for r∈\[aj,aj+1)𝑟subscript𝑎𝑗subscript𝑎𝑗1r\\in\[a\_{j},a\_{j+1}). In particular, V​(A,r)\=V​(A,aj)𝑉𝐴𝑟𝑉𝐴subscript𝑎𝑗V(A,r)=V(A,a\_{j}) for r∈\[aj,aj+1)𝑟subscript𝑎𝑗subscript𝑎𝑗1r\\in\[a\_{j},a\_{j+1}). Thus using Lemma [3.5](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.Thmthm5 "Lemma 3.5. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
, we conclude that V​(A,r)𝑉𝐴𝑟V(A,r) is spanned by the set of eigenvectors of D𝐷D with eigenvalue-modulus less than or equal to ajsubscript𝑎𝑗a\_{j}. ∎\
\
###### Theorem 3.8.\
\
Let A∈Mm​(ℂ)𝐴subscript𝑀𝑚ℂA\\in M\_{m}(\\mathbb{C}) and {a1,…,ak}subscript𝑎1…subscript𝑎𝑘\\{a\_{1},\\ldots,a\_{k}\\} be the set of modulus of eigenvalues of A𝐴A such that 0≤a1<a2<⋯<ak0subscript𝑎1subscript𝑎2⋯subscript𝑎𝑘0\\leq a\_{1}<a\_{2}<\\cdots<a\_{k}. Let A\=D+N𝐴𝐷𝑁A=D+N be the Jordan-Chevalley decomposition of A𝐴A into its commuting diagonalizable and nilpotent parts (D,N𝐷𝑁D,N, respectively). For 1≤j≤k1𝑗𝑘1\\leq j\\leq k, let Ejsubscript𝐸𝑗E\_{j} be the orthogonal projection onto the subspace of ℂmsuperscriptℂ𝑚\\mathbb{C}^{m} spanned by the eigenvectors of D𝐷D corresponding to eigenvalues with modulus less than or equal to ajsubscript𝑎𝑗a\_{j}, and set E0:=0assignsubscript𝐸00E\_{0}:=0. Then the following assertions hold:\
\
*   (i)\
    \
    The sequence {|An|1n}n∈ℕsubscriptsuperscriptsuperscript𝐴𝑛1𝑛𝑛ℕ\\{|A^{n}|^{\\frac{1}{n}}\\}\_{n\\in\\mathbb{N}} converges to the positive-semidefinite matrix ∑i\=1kaj​(Ej−Ej−1).superscriptsubscript𝑖1𝑘subscript𝑎𝑗subscript𝐸𝑗subscript𝐸𝑗1\\sum\_{i=1}^{k}a\_{j}(E\_{j}-E\_{j-1}).\
    \
*   (ii)\
    \
    A non-zero vector x→∈ℂm→𝑥superscriptℂ𝑚\\vec{x}\\in\\mathbb{C}^{m} is in ran​(Ej)\\ran​(Ej−1)\\ransubscript𝐸𝑗ransubscript𝐸𝑗1\\mathrm{ran}(E\_{j})\\backslash\\mathrm{ran}(E\_{j-1}) if and only if limn→∞‖An​x→‖1n\=aj.subscript→𝑛superscriptnormsuperscript𝐴𝑛→𝑥1𝑛subscript𝑎𝑗\\lim\_{n\\to\\infty}\\|A^{n}\\vec{x}\\|^{\\frac{1}{n}}=a\_{j}.\
    \
*   (iii)\
    \
    The set ran​(Ej)\\ran​(Ej−1)\\ransubscript𝐸𝑗ransubscript𝐸𝑗1\\mathrm{ran}(E\_{j})\\backslash\\mathrm{ran}(E\_{j-1}) is invariant under the action of Aksuperscript𝐴𝑘A^{k} for every k∈ℕ𝑘ℕk\\in\\mathbb{N}.\
    \
\
###### Proof.\
\
(i) Let H1,H2subscript𝐻1subscript𝐻2H\_{1},H\_{2} be limit points of the sequence {|An|1n}n∈ℕsubscriptsuperscriptsuperscript𝐴𝑛1𝑛𝑛ℕ\\{|A^{n}|^{\\frac{1}{n}}\\}\_{n\\in\\mathbb{N}}. By Proposition [3.7](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.Thmthm7 "Proposition 3.7. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
, V​(A,r)\=V​(H1,r)\=V​(H2,r)𝑉𝐴𝑟𝑉subscript𝐻1𝑟𝑉subscript𝐻2𝑟V(A,r)=V(H\_{1},r)=V(H\_{2},r) for all r≥0𝑟0r\\geq 0. By Lemma [3.6](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.Thmthm6 "Lemma 3.6. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
, H1\=H2subscript𝐻1subscript𝐻2H\_{1}=H\_{2}. Hence the sequence {|An|1n}n∈ℕsubscriptsuperscriptsuperscript𝐴𝑛1𝑛𝑛ℕ\\{|A^{n}|^{\\frac{1}{n}}\\}\_{n\\in\\mathbb{N}} converges. The description of Ejsubscript𝐸𝑗E\_{j} also follows from Proposition [3.7](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.Thmthm7 "Proposition 3.7. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
 and Lemma [3.6](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.Thmthm6 "Lemma 3.6. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
.\
\
(ii) For y→∈ℂm→𝑦superscriptℂ𝑚\\vec{y}\\in\\mathbb{C}^{m} if limn→∞‖An​y→‖1n\=ajsubscript→𝑛superscriptnormsuperscript𝐴𝑛→𝑦1𝑛subscript𝑎𝑗\\lim\_{n\\to\\infty}\\|A^{n}\\vec{y}\\|^{\\frac{1}{n}}=a\_{j}, from the definition of V​(A,aj)𝑉𝐴subscript𝑎𝑗V(A,a\_{j}) and V​(A,aj−1)𝑉𝐴subscript𝑎𝑗1V(A,a\_{j-1}), it follows that y→∈V​(A,aj)\\V​(A,aj−1)→𝑦\\𝑉𝐴subscript𝑎𝑗𝑉𝐴subscript𝑎𝑗1\\vec{y}\\in V(A,a\_{j})\\backslash V(A,a\_{j-1}).\
\
The converse needs a bit more work. Define Hk:=|Ak|1kassignsubscript𝐻𝑘superscriptsuperscript𝐴𝑘1𝑘H\_{k}:=|A^{k}|^{\\frac{1}{k}} for k∈ℕ𝑘ℕk\\in\\mathbb{N}. From part (i), Hn→H→subscript𝐻𝑛𝐻H\_{n}\\to H as n→∞→𝑛n\\to\\infty for some positive-semidefinite matrix in Mm​(ℂ)subscript𝑀𝑚ℂM\_{m}(\\mathbb{C}). Thus Hnm→Hm→superscriptsubscript𝐻𝑛𝑚superscript𝐻𝑚H\_{n}^{m}\\to H^{m} as n→∞→𝑛n\\to\\infty for every m∈ℕ𝑚ℕm\\in\\mathbb{N}. By Lemma [2.8](https://ar5iv.labs.arxiv.org/html/2303.01252#S2.Thmthm8 "Lemma 2.8. ‣ 2.2. Singular values of matrices ‣ 2. Preparatory results ‣ A stronger form of Yamamoto’s theorem on singular values")\
 (considering α\=mn𝛼𝑚𝑛\\alpha=\\frac{m}{n} with sufficiently large n𝑛n so that α∈\[0,1\]𝛼01\\alpha\\in\[0,1\]), for every m∈ℕ𝑚ℕm\\in\\mathbb{N} and y→∈ℂm→𝑦superscriptℂ𝑚\\vec{y}\\in\\mathbb{C}^{m}, we have\
\
|     |     |     |\
| --- | --- | --- |\
|     | ‖Hm​y→‖1m\=limn→∞‖Hnm​y→‖1m≤lim infn→∞‖An​y→‖1n≤lim supn→∞‖An​y→‖1n.superscriptnormsuperscript𝐻𝑚→𝑦1𝑚subscript→𝑛superscriptnormsuperscriptsubscript𝐻𝑛𝑚→𝑦1𝑚subscriptlimit-infimum→𝑛superscriptnormsuperscript𝐴𝑛→𝑦1𝑛subscriptlimit-supremum→𝑛superscriptnormsuperscript𝐴𝑛→𝑦1𝑛\\\|H^{m}\\vec{y}\\\|^{\\frac{1}{m}}=\\lim\_{n\\to\\infty}\\\|H\_{n}^{m}\\vec{y}\\\|^{\\frac{1}{m}}\\leq\\liminf\_{n\\to\\infty}\\\|A^{n}\\vec{y}\\\|^{\\frac{1}{n}}\\leq\\limsup\_{n\\to\\infty}\\\|A^{n}\\vec{y}\\\|^{\\frac{1}{n}}. |     |\
\
By Proposition [3.7](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.Thmthm7 "Proposition 3.7. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
, ran​(Ej)\=V​(A,aj)\=V​(H,aj)ransubscript𝐸𝑗𝑉𝐴subscript𝑎𝑗𝑉𝐻subscript𝑎𝑗\\mathrm{ran}(E\_{j})=V(A,a\_{j})=V(H,a\_{j}). If x→∈V​(A,aj)\\V​(A,aj−1)→𝑥\\𝑉𝐴subscript𝑎𝑗𝑉𝐴subscript𝑎𝑗1\\vec{x}\\in V(A,a\_{j})\\backslash V(A,a\_{j-1}), note that\
\
|     |     |     |\
| --- | --- | --- |\
|     | aj\=limm→∞‖Hm​x→‖1m≤lim infn→∞‖An​x→‖1n≤lim supn→∞‖An​y→‖1n≤aj.subscript𝑎𝑗subscript→𝑚superscriptnormsuperscript𝐻𝑚→𝑥1𝑚subscriptlimit-infimum→𝑛superscriptnormsuperscript𝐴𝑛→𝑥1𝑛subscriptlimit-supremum→𝑛superscriptnormsuperscript𝐴𝑛→𝑦1𝑛subscript𝑎𝑗a\_{j}=\\lim\_{m\\to\\infty}\\\|H^{m}\\vec{x}\\\|^{\\frac{1}{m}}\\leq\\liminf\_{n\\to\\infty}\\\|A^{n}\\vec{x}\\\|^{\\frac{1}{n}}\\leq\\limsup\_{n\\to\\infty}\\\|A^{n}\\vec{y}\\\|^{\\frac{1}{n}}\\leq a\_{j}. |     |\
\
Thus limn→∞‖An​x→‖1n\=ajsubscript→𝑛superscriptnormsuperscript𝐴𝑛→𝑥1𝑛subscript𝑎𝑗\\lim\_{n\\to\\infty}\\|A^{n}\\vec{x}\\|^{\\frac{1}{n}}=a\_{j}.\
\
(iii) Note that for fixed k∈ℕ𝑘ℕk\\in\\mathbb{N}, we have\
\
|     |     |     |\
| --- | --- | --- |\
|     | limn→∞‖An​x→‖1n\=limn→∞‖An+k​x→‖1n+k\=limn→∞‖An+k​x→‖1n\=limn→∞‖An​(Ak​x→)‖1n.subscript→𝑛superscriptnormsuperscript𝐴𝑛→𝑥1𝑛subscript→𝑛superscriptnormsuperscript𝐴𝑛𝑘→𝑥1𝑛𝑘subscript→𝑛superscriptnormsuperscript𝐴𝑛𝑘→𝑥1𝑛subscript→𝑛superscriptnormsuperscript𝐴𝑛superscript𝐴𝑘→𝑥1𝑛\\lim\_{n\\to\\infty}\\\|A^{n}\\vec{x}\\\|^{\\frac{1}{n}}=\\lim\_{n\\to\\infty}\\\|A^{n+k}\\vec{x}\\\|^{\\frac{1}{n+k}}=\\lim\_{n\\to\\infty}\\\|A^{n+k}\\vec{x}\\\|^{\\frac{1}{n}}=\\lim\_{n\\to\\infty}\\\|A^{n}(A^{k}\\vec{x})\\\|^{\\frac{1}{n}}. |     |\
\
The assertion follows from part (ii). ∎\
\
###### Corollary 3.9 (Yamamoto’s theorem).\
\
Let A∈Mm​(ℂ)𝐴subscript𝑀𝑚ℂA\\in M\_{m}(\\mathbb{C}) with its jthsuperscript𝑗thj^{\\mathrm{th}}\-largest singular value denoted by sj​(A)subscript𝑠𝑗𝐴s\_{j}(A), and jthsuperscript𝑗thj^{\\mathrm{th}} largest eigenvalue-modulus denoted by |λj|​(A)subscript𝜆𝑗𝐴|\\lambda\_{j}|(A). Then for all 1≤j≤m1𝑗𝑚1\\leq j\\leq m, we have\
\
|     |     |     |\
| --- | --- | --- |\
|     | limn→∞sj​(An)1n\=\|λj\|​(A).subscript→𝑛subscript𝑠𝑗superscriptsuperscript𝐴𝑛1𝑛subscript𝜆𝑗𝐴\\lim\_{n\\to\\infty}s\_{j}(A^{n})^{\\frac{1}{n}}=\|\\lambda\_{j}\|(A). |     |\
\
###### Proof.\
\
Note that sj​(An)1n\=sj​(|An|1n)subscript𝑠𝑗superscriptsuperscript𝐴𝑛1𝑛subscript𝑠𝑗superscriptsuperscript𝐴𝑛1𝑛s\_{j}(A^{n})^{\\frac{1}{n}}=s\_{j}(|A^{n}|^{\\frac{1}{n}}). Let H\=limn→∞|An|1n𝐻subscript→𝑛superscriptsuperscript𝐴𝑛1𝑛H=\\lim\_{n\\to\\infty}|A^{n}|^{\\frac{1}{n}} (this limit exists by Theorem [3.8](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.Thmthm8 "Theorem 3.8. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
). From Lemma [2.4](https://ar5iv.labs.arxiv.org/html/2303.01252#S2.Thmthm4 "Lemma 2.4. ‣ 2.2. Singular values of matrices ‣ 2. Preparatory results ‣ A stronger form of Yamamoto’s theorem on singular values")\
 and Proposition [3.3](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.Thmthm3 "Proposition 3.3. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
\-(iii), we conclude that\
\
|     |     |     |\
| --- | --- | --- |\
|     | limn→∞sj​(An)1n\=sj​(H)\=\|λj\|​(H)\=\|λj\|​(A).subscript→𝑛subscript𝑠𝑗superscriptsuperscript𝐴𝑛1𝑛subscript𝑠𝑗𝐻subscript𝜆𝑗𝐻subscript𝜆𝑗𝐴\\lim\_{n\\to\\infty}s\_{j}(A^{n})^{\\frac{1}{n}}=s\_{j}(H)=\|\\lambda\_{j}\|(H)=\|\\lambda\_{j}\|(A). |     |\
\
∎\
\
4\. Applications to linear systems of ordinary differential equations\
---------------------------------------------------------------------\
\
In this section, we discuss the insights provided by Theorem [3.8](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.Thmthm8 "Theorem 3.8. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
 to the study of linear systems of ordinary differential equations with constant coefficients. We consistently use the notation from Theorem [4.1](https://ar5iv.labs.arxiv.org/html/2303.01252#S4.Thmthm1 "Theorem 4.1. ‣ 4. Applications to linear systems of ordinary differential equations ‣ A stronger form of Yamamoto’s theorem on singular values")\
 below throughout this section.\
\
###### Theorem 4.1.\
\
Let A∈Mm​(ℂ)𝐴subscript𝑀𝑚ℂA\\in M\_{m}(\\mathbb{C}) and {h1,…,hk}subscriptℎ1…subscriptℎ𝑘\\{h\_{1},\\ldots,h\_{k}\\} be the set of real-parts of eigenvalues of A𝐴A such that h1<h2<⋯<hksubscriptℎ1subscriptℎ2⋯subscriptℎ𝑘h\_{1}<h\_{2}<\\cdots<h\_{k}. Let A\=D+N𝐴𝐷𝑁A=D+N be the Jordan-Chevalley decomposition of A𝐴A into its commuting diagonalizable and nilpotent parts (D,N𝐷𝑁D,N, respectively). For 1≤j≤k1𝑗𝑘1\\leq j\\leq k, let Fjsubscript𝐹𝑗F\_{j} be the orthogonal projection onto the subspace of ℂmsuperscriptℂ𝑚\\mathbb{C}^{m} spanned by the eigenvectors of D𝐷D corresponding to eigenvalues with real-part less than or equal to hjsubscriptℎ𝑗h\_{j}, and set E0:=0assignsubscript𝐸00E\_{0}:=0. Then the following assertions hold:\
\
*   (i)\
    \
    limt→∞|et​A|1t\=∑i\=1kehj​(Fj−Fj−1).subscript→𝑡superscriptsuperscript𝑒𝑡𝐴1𝑡superscriptsubscript𝑖1𝑘superscript𝑒subscriptℎ𝑗subscript𝐹𝑗subscript𝐹𝑗1\\lim\_{t\\to\\infty}|e^{tA}|^{\\frac{1}{t}}=\\sum\_{i=1}^{k}e^{h\_{j}}(F\_{j}-F\_{j-1}).\
    \
*   (ii)\
    \
    A non-zero vector x→∈ℂm→𝑥superscriptℂ𝑚\\vec{x}\\in\\mathbb{C}^{m} is in ran​(Fj)\\ran​(Fj−1)\\ransubscript𝐹𝑗ransubscript𝐹𝑗1\\mathrm{ran}(F\_{j})\\backslash\\mathrm{ran}(F\_{j-1}) if and only if limt→∞‖et​A​x→‖1t\=ehj.subscript→𝑡superscriptnormsuperscript𝑒𝑡𝐴→𝑥1𝑡superscript𝑒subscriptℎ𝑗\\lim\_{t\\to\\infty}\\|e^{tA}\\vec{x}\\|^{\\frac{1}{t}}=e^{h\_{j}}.\
    \
*   (iii)\
    \
    The set ran​(Fj)\\ran​(Fj−1)\\ransubscript𝐹𝑗ransubscript𝐹𝑗1\\mathrm{ran}(F\_{j})\\backslash\\mathrm{ran}(F\_{j-1}) is invariant under the action of es​Asuperscript𝑒𝑠𝐴e^{sA} for every s≥0𝑠0s\\geq 0.\
    \
\
###### Proof.\
\
We note three pertinent observations regarding exponentials of matrices and complex numbers.\
\
*   (a)\
    \
    The Jordan-Chevalley decomposition of eAsuperscript𝑒𝐴e^{A} is given by eA\=eD+eD​(eN−I)superscript𝑒𝐴superscript𝑒𝐷superscript𝑒𝐷superscript𝑒𝑁𝐼e^{A}=e^{D}+e^{D}(e^{N}-I) so that eDsuperscript𝑒𝐷e^{D} is the diagonalizable part of eAsuperscript𝑒𝐴e^{A}.\
    \
*   (b)\
    \
    A vector x→→𝑥\\vec{x} is an eigenvector of D𝐷D with eigenvalue λ𝜆\\lambda if and only if x→→𝑥\\vec{x} is an eigenvector of eDsuperscript𝑒𝐷e^{D} with eigenvalue eλsuperscript𝑒𝜆e^{\\lambda}.\
    \
*   (c)\
    \
    For λ1,λ2∈ℂsubscript𝜆1subscript𝜆2ℂ\\lambda\_{1},\\lambda\_{2}\\in\\mathbb{C}, we have |eλ1|<|eλ2|superscript𝑒subscript𝜆1superscript𝑒subscript𝜆2|e^{\\lambda\_{1}}|<|e^{\\lambda\_{2}}| (|eλ1|\=|eλ2|superscript𝑒subscript𝜆1superscript𝑒subscript𝜆2|e^{\\lambda\_{1}}|=|e^{\\lambda\_{2}}|, respectively) if and only if ℜ⁡λ1<ℜ⁡λ2subscript𝜆1subscript𝜆2\\Re\\lambda\_{1}<\\Re\\lambda\_{2} (ℜ⁡λ1\=ℜ⁡λ2subscript𝜆1subscript𝜆2\\Re\\lambda\_{1}=\\Re\\lambda\_{2}, respectively)\
    \
\
Applying Theorem [3.8](https://ar5iv.labs.arxiv.org/html/2303.01252#S3.Thmthm8 "Theorem 3.8. ‣ 3. The Main Theorem ‣ A stronger form of Yamamoto’s theorem on singular values")\
 to the matrix eAsuperscript𝑒𝐴e^{A}, we conclude that\
\
|     |     |     |\
| --- | --- | --- |\
|     | limn→∞\|en​A\|1n\=∑i\=1kehj​(Fj−Fj−1),subscript→𝑛superscriptsuperscript𝑒𝑛𝐴1𝑛superscriptsubscript𝑖1𝑘superscript𝑒subscriptℎ𝑗subscript𝐹𝑗subscript𝐹𝑗1\\lim\_{n\\to\\infty}\|e^{nA}\|^{\\frac{1}{n}}=\\sum\_{i=1}^{k}e^{h\_{j}}(F\_{j}-F\_{j-1}), |     |\
\
and a vector x→∈ℂm→𝑥superscriptℂ𝑚\\vec{x}\\in\\mathbb{C}^{m} is in ran​(Fj)\\ran​(Fj−1)\\ransubscript𝐹𝑗ransubscript𝐹𝑗1\\mathrm{ran}(F\_{j})\\backslash\\mathrm{ran}(F\_{j-1}) if and only if limn→∞‖en​A​x→‖1n\=ehj.subscript→𝑛superscriptnormsuperscript𝑒𝑛𝐴→𝑥1𝑛superscript𝑒subscriptℎ𝑗\\lim\_{n\\to\\infty}\\|e^{nA}\\vec{x}\\|^{\\frac{1}{n}}=e^{h\_{j}}. What remains to be proved is that the limits in (i) and (ii) exist as t→∞→𝑡t\\to\\infty in ℝℝ\\mathbb{R} and are equal to their respective limits as n→∞→𝑛n\\to\\infty in ℕℕ\\mathbb{N}.\
\
Note that the function t↦‖et​A‖maps-to𝑡normsuperscript𝑒𝑡𝐴t\\mapsto\\|e^{tA}\\| is continuous and only takes strictly positive values as et​Asuperscript𝑒𝑡𝐴e^{tA} is invertible for any t∈ℝ𝑡ℝt\\in\\mathbb{R}. Let c:=mint∈\[0,1\]⁡‖e−t​A‖−1assign𝑐subscript𝑡01superscriptnormsuperscript𝑒𝑡𝐴1c:=\\min\_{t\\in\[0,1\]}\\|e^{-tA}\\|^{-1} and C:=maxt∈\[0,1\]⁡‖et​A‖assign𝐶subscript𝑡01normsuperscript𝑒𝑡𝐴C:=\\max\_{t\\in\[0,1\]}\\|e^{tA}\\|. Clearly 0<c≤C0𝑐𝐶0<c\\leq C. For α∈\[0,1)𝛼01\\alpha\\in\[0,1), we have c2​I≤(eα​A)∗​eα​A≤C2​Isuperscript𝑐2𝐼superscriptsuperscript𝑒𝛼𝐴superscript𝑒𝛼𝐴superscript𝐶2𝐼c^{2}I\\leq(e^{\\alpha A})^{\*}e^{\\alpha A}\\leq C^{2}I. For every positive integer n𝑛n, we note that\
\
|     |     |     |     |\
| --- | --- | --- | --- |\
| (4.1) |     | c2​(en​A)∗​en​A≤(e(n+α)​A)∗​e(n+α)​A≤C2​(en​A)∗​en​Asuperscript𝑐2superscriptsuperscript𝑒𝑛𝐴superscript𝑒𝑛𝐴superscriptsuperscript𝑒𝑛𝛼𝐴superscript𝑒𝑛𝛼𝐴superscript𝐶2superscriptsuperscript𝑒𝑛𝐴superscript𝑒𝑛𝐴c^{2}(e^{nA})^{\*}e^{nA}\\leq(e^{(n+\\alpha)A})^{\*}e^{(n+\\alpha)A}\\leq C^{2}(e^{nA})^{\*}e^{nA} |     |\
\
As x↦x12​nmaps-to𝑥superscript𝑥12𝑛x\\mapsto x^{\\frac{1}{2n}} is an operator-monotone function on \[0,∞)0\[0,\\infty), we observe that\
\
|     |     |     |\
| --- | --- | --- |\
|     | c1n​\|en​A\|1n≤\|e(n+α)​A\|1n≤C1n​\|en​A\|1n.superscript𝑐1𝑛superscriptsuperscript𝑒𝑛𝐴1𝑛superscriptsuperscript𝑒𝑛𝛼𝐴1𝑛superscript𝐶1𝑛superscriptsuperscript𝑒𝑛𝐴1𝑛c^{\\frac{1}{n}}\|e^{nA}\|^{\\frac{1}{n}}\\leq\|e^{(n+\\alpha)A}\|^{\\frac{1}{n}}\\leq C^{\\frac{1}{n}}\|e^{nA}\|^{\\frac{1}{n}}. |     |\
\
Since limn→∞c1n\=limn→∞C1n\=1subscript→𝑛superscript𝑐1𝑛subscript→𝑛superscript𝐶1𝑛1\\lim\_{n\\to\\infty}c^{\\frac{1}{n}}=\\lim\_{n\\to\\infty}C^{\\frac{1}{n}}=1 and limt→∞⌊t⌋t\=1subscript→𝑡𝑡𝑡1\\lim\_{t\\to\\infty}\\frac{\\lfloor t\\rfloor}{t}=1, we conclude that\
\
|     |     |     |\
| --- | --- | --- |\
|     | limt→∞\|et​A\|1t\=limt→∞\|et​A\|1⌊t⌋\=limn→∞\|en​A\|1n.subscript→𝑡superscriptsuperscript𝑒𝑡𝐴1𝑡subscript→𝑡superscriptsuperscript𝑒𝑡𝐴1𝑡subscript→𝑛superscriptsuperscript𝑒𝑛𝐴1𝑛\\lim\_{t\\to\\infty}\|e^{tA}\|^{\\frac{1}{t}}=\\lim\_{t\\to\\infty}\|e^{tA}\|^{\\frac{1}{\\lfloor t\\rfloor}}=\\lim\_{n\\to\\infty}\|e^{nA}\|^{\\frac{1}{n}}. |     |\
\
For every x→∈ℂm→𝑥superscriptℂ𝑚\\vec{x}\\in\\mathbb{C}^{m}, from inequality ([4.1](https://ar5iv.labs.arxiv.org/html/2303.01252#S4.E1 "In Proof. ‣ 4. Applications to linear systems of ordinary differential equations ‣ A stronger form of Yamamoto’s theorem on singular values")\
) we have that\
\
|     |     |     |\
| --- | --- | --- |\
|     | c1n​‖en​A​x→‖1n≤‖e(n+α)​A​x→‖1n≤C1n​‖en​A​x→‖1n.superscript𝑐1𝑛superscriptnormsuperscript𝑒𝑛𝐴→𝑥1𝑛superscriptnormsuperscript𝑒𝑛𝛼𝐴→𝑥1𝑛superscript𝐶1𝑛superscriptnormsuperscript𝑒𝑛𝐴→𝑥1𝑛c^{\\frac{1}{n}}\\\|e^{nA}\\vec{x}\\\|^{\\frac{1}{n}}\\leq\\\|e^{(n+\\alpha)A}\\vec{x}\\\|^{\\frac{1}{n}}\\leq C^{\\frac{1}{n}}\\\|e^{nA}\\vec{x}\\\|^{\\frac{1}{n}}. |     |\
\
Thus\
\
|     |     |     |\
| --- | --- | --- |\
|     | limt→∞‖et​A​x→‖1t\=limt→∞‖et​A‖1⌊t⌋\=limn→∞‖en​A​x→‖1n.subscript→𝑡superscriptnormsuperscript𝑒𝑡𝐴→𝑥1𝑡subscript→𝑡superscriptnormsuperscript𝑒𝑡𝐴1𝑡subscript→𝑛superscriptnormsuperscript𝑒𝑛𝐴→𝑥1𝑛\\lim\_{t\\to\\infty}\\\|e^{tA}\\vec{x}\\\|^{\\frac{1}{t}}=\\lim\_{t\\to\\infty}\\\|e^{tA}\\\|^{\\frac{1}{\\lfloor t\\rfloor}}=\\lim\_{n\\to\\infty}\\\|e^{nA}\\vec{x}\\\|^{\\frac{1}{n}}. |     |\
\
Part (iii) follows from part (ii) together with the fact that for fixed s≥0𝑠0s\\geq 0, we have\
\
|     |     |     |\
| --- | --- | --- |\
|     | limt→∞‖et​A​x→‖1t\=limt→∞‖e(t+s)​A​x→‖1t+s\=limt→∞‖e(t+s)​A​x→‖1t\=limt→∞‖et​A​(es​A​x→)‖1t.subscript→𝑡superscriptnormsuperscript𝑒𝑡𝐴→𝑥1𝑡subscript→𝑡superscriptnormsuperscript𝑒𝑡𝑠𝐴→𝑥1𝑡𝑠subscript→𝑡superscriptnormsuperscript𝑒𝑡𝑠𝐴→𝑥1𝑡subscript→𝑡superscriptnormsuperscript𝑒𝑡𝐴superscript𝑒𝑠𝐴→𝑥1𝑡\\lim\_{t\\to\\infty}\\\|e^{tA}\\vec{x}\\\|^{\\frac{1}{t}}=\\lim\_{t\\to\\infty}\\\|e^{(t+s)A}\\vec{x}\\\|^{\\frac{1}{t+s}}=\\lim\_{t\\to\\infty}\\\|e^{(t+s)A}\\vec{x}\\\|^{\\frac{1}{t}}=\\lim\_{t\\to\\infty}\\\|e^{tA}(e^{sA}\\vec{x})\\\|^{\\frac{1}{t}}. |     |\
\
∎\
\
Consider the linear homogeneous system of differential equations with constant coefficients,\
\
|     |     |     |     |\
| --- | --- | --- | --- |\
| (4.2) |     | d​xid​t\=∑j\=1mai​j​xj,i\=1,2,…,m,formulae-sequence𝑑subscript𝑥𝑖𝑑𝑡superscriptsubscript𝑗1𝑚subscript𝑎𝑖𝑗subscript𝑥𝑗𝑖12…𝑚\\frac{dx\_{i}}{dt}=\\sum\_{j=1}^{m}a\_{ij}x\_{j},\\;\\;i=1,2,\\ldots,m, |     |\
\
that is,\
\
|     |     |     |\
| --- | --- | --- |\
|     | d​X→d​t\=A​X→,𝑑→𝑋𝑑𝑡𝐴→𝑋\\frac{d\\vec{X}}{dt}=A\\vec{X}, |     |\
\
where X→\=(x1,…,xm)T:ℝ→ℂm:→𝑋superscriptsubscript𝑥1…subscript𝑥𝑚𝑇→ℝsuperscriptℂ𝑚\\vec{X}=(x\_{1},\\ldots,x\_{m})^{T}:\\mathbb{R}\\to\\mathbb{C}^{m}. The unique solution to the above system is given by X→​(t)\=et​A​X→​(0)→𝑋𝑡superscript𝑒𝑡𝐴→𝑋0\\vec{X}(t)=e^{tA}\\vec{X}(0), where X→​(0)→𝑋0\\vec{X}(0) denotes the vector of initial conditions (see \[[3](https://ar5iv.labs.arxiv.org/html/2303.01252#bib.bib3)\
, Corollary 4.3\]).\
\
Observation 1: Let λ𝜆\\lambda be an eigenvalue of A𝐴A so that ℜ⁡λ\=hj𝜆subscriptℎ𝑗\\Re\\lambda=h\_{j} for some 1≤j≤k1𝑗𝑘1\\leq j\\leq k. From Theorem [4.1](https://ar5iv.labs.arxiv.org/html/2303.01252#S4.Thmthm1 "Theorem 4.1. ‣ 4. Applications to linear systems of ordinary differential equations ‣ A stronger form of Yamamoto’s theorem on singular values")\
\-(ii), it follows that if X→​(0)∈ran​(Fj)\\ran​(Fj−1)→𝑋0\\ransubscript𝐹𝑗ransubscript𝐹𝑗1\\vec{X}(0)\\in\\mathrm{ran}(F\_{j})\\backslash\\mathrm{ran}(F\_{j-1}), there exist M≥1𝑀1M\\geq 1 and N\>0𝑁0N>0 such that\
\
|     |     |     |\
| --- | --- | --- |\
|     | N​eρ​t​‖X→​(0)‖≤‖X→​(t)‖≤M​eω​t​‖X→​(0)‖,𝑁superscript𝑒𝜌𝑡norm→𝑋0norm→𝑋𝑡𝑀superscript𝑒𝜔𝑡norm→𝑋0Ne^{\\rho t}\\\|\\vec{X}(0)\\\|\\leq\\\|\\vec{X}(t)\\\|\\leq Me^{\\omega t}\\\|\\vec{X}(0)\\\|, |     |\
\
for all t≥0𝑡0t\\geq 0, and ρ<hj<ω𝜌subscriptℎ𝑗𝜔\\rho<h\_{j}<\\omega. This gives us a slightly stronger version of \[[3](https://ar5iv.labs.arxiv.org/html/2303.01252#bib.bib3)\
, Theorem 4.5(a)\] which provides the above bounds only in the cases where X→​(0)→𝑋0\\vec{X}(0) is an eigenvector of D𝐷D with eigenvalue λ𝜆\\lambda. (Note that the λ𝜆\\lambda\-eigenspace of D𝐷D is contained in ran​(Fj)\\ran​(Fj−1)\\ransubscript𝐹𝑗ransubscript𝐹𝑗1\\mathrm{ran}(F\_{j})\\backslash\\mathrm{ran}(F\_{j-1})).\
\
Observation 2: If the vector of initial conditions, X→​(0)→𝑋0\\vec{X}(0), is in ran​(Fj)\\ran​(Fj−1)\\ransubscript𝐹𝑗ransubscript𝐹𝑗1\\mathrm{ran}(F\_{j})\\backslash\\mathrm{ran}(F\_{j-1}), then from Theorem [4.1](https://ar5iv.labs.arxiv.org/html/2303.01252#S4.Thmthm1 "Theorem 4.1. ‣ 4. Applications to linear systems of ordinary differential equations ‣ A stronger form of Yamamoto’s theorem on singular values")\
\-(iii), it follows that X→​(t)→𝑋𝑡\\vec{X}(t) is in ran​(Fj)\\ran​(Fj−1)\\ransubscript𝐹𝑗ransubscript𝐹𝑗1\\mathrm{ran}(F\_{j})\\backslash\\mathrm{ran}(F\_{j-1}) for all t≥0𝑡0t\\geq 0.\
\
In other words, the above observation tells us that if the vector of initial conditions, X→​(0)→𝑋0\\vec{X}(0), is not in the region Ω:=ran​(Fj−1)∪(ℂm\\ran​(Fj))assignΩransubscript𝐹𝑗1\\superscriptℂ𝑚ransubscript𝐹𝑗\\Omega:=\\mathrm{ran}(F\_{j-1})\\cup\\big{(}\\mathbb{C}^{m}\\backslash\\mathrm{ran}(F\_{j})\\big{)}, then X→​(t)→𝑋𝑡\\vec{X}(t) avoids the region ΩΩ\\Omega for all t≥0𝑡0t\\geq 0.\
\
5\. Acknowledgements\
--------------------\
\
This work is supported by the Startup Research Grant (SRG/2021/002383) of SERB (Science and Engineering Research Board, Govt. of India). I would like to express my gratitude to B. V. Rajarama Bhat for discussions and suggestions that helped improve the presentation in this article.\
\
References\
----------\
\
*   \[1\] Rajendra Bhatia. Matrix Analysis, volume 169. Springer, 1997.\
*   \[2\] Wayne D. Blizard. Multiset theory. Notre Dame J. Formal Logic, 30(1):36–66, 1989.\
*   \[3\] András Bátkai, Marjeta Kramar Fijavž, and Abdelaziz Rhandi. Positive Operator Semigroups: From Finite to Infinite Dimensions, volume 257. Birkhäuser, 2017.\
*   \[4\] Werner Gautschi. The asymptotic behaviour of powers of matrices. Duke Math. J., 20:127–140, 1953.\
*   \[5\] Werner Gautschi. The asymptotic behaviour of powers of matrices. II. Duke Math. J., 20:375–379, 1953.\
*   \[6\] Uffe Haagerup and Hanne Schultz. Invariant subspaces for operators in a general II1subscriptII1\\text{II}\_{1}\-factor. Publ. Math., Inst. Hautes Étud. Sci., 109:19–111, 2009.\
*   \[7\] Roy Mathias. Two theorems on singular values and eigenvalues. Am. Math. Mon., 97(1):47–50, 1990.\
*   \[8\] Tin-Yau Tam and Huajun Huang. An extension of Yamamoto’s theorem on the eigenvalues and singular values of a matrix. J. Math. Soc. Japan, 58(4):1197–1202, 2006.\
*   \[9\] Tetsuro Yamamoto. On the extreme values of the roots of matrices. J. Math. Soc. Japan, 19:173–178, 1967.\
\
[◄](https://ar5iv.labs.arxiv.org/html/2303.01251)\
 [![ar5iv homepage](https://ar5iv.labs.arxiv.org/assets/ar5iv.png)](https://ar5iv.labs.arxiv.org/)\
 [Feeling  \
lucky?](https://ar5iv.labs.arxiv.org/feeling_lucky)\
 [](https://ar5iv.labs.arxiv.org/land_of_honey_and_milk)\
[Conversion  \
report](https://ar5iv.labs.arxiv.org/log/2303.01252)\
 [Report  \
an issue](https://github.com/dginev/ar5iv/issues/new?template=improve-article--arxiv-id-.md&title=Improve+article+2303.01252)\
 [View original  \
on arXiv](https://arxiv.org/abs/2303.01252)\
[►](https://ar5iv.labs.arxiv.org/html/2303.01253)\
\
[](javascript:toggleColorScheme() "Toggle ar5iv color scheme")\
[Copyright](https://arxiv.org/help/license)\
 [Privacy Policy](https://arxiv.org/help/policies/privacy_policy)\
\
Generated on Thu Feb 29 21:49:08 2024 by [LaTeXML![Mascot Sammy](<Base64-Image-Removed>)](http://dlmf.nist.gov/LaTeXML/)
