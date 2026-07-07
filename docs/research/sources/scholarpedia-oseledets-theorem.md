Typesetting math: 100%

Scholarpedia is supported by [Brain Corporation](https://www.braincorp.com/)

Oseledets theorem
=================

From Scholarpedia

|     |     |     |
| --- | --- | --- |
| Valery Oseledets (2008), Scholarpedia, 3(1):1846. | [doi:10.4249/scholarpedia.1846](http://dx.doi.org/10.4249/scholarpedia.1846) | revision #142085 \[[link to/cite this article](http://www.scholarpedia.org/w/index.php?title=Oseledets_theorem&action=cite&rev=142085 "Oseledets theorem")<br>\] |

Jump to: [navigation](http://www.scholarpedia.org/article/Oseledets_theorem#mw-head)
, [search](http://www.scholarpedia.org/article/Oseledets_theorem#p-search)

**Post-publication activity**  

Curator: [Valery Oseledets](http://www.scholarpedia.org/article/User:Valery_Oseledets "User:Valery Oseledets")

Contributors:

0.44 -

[Eugene M. Izhikevich](http://www.scholarpedia.org/article/User:Eugene_M._Izhikevich "User:Eugene M. Izhikevich")

0.22 -

[Nick Orbeck](http://www.scholarpedia.org/article/User:Nick_Orbeck "User:Nick Orbeck")

0.22 -

[James Meiss](http://www.scholarpedia.org/article/User:James_Meiss "User:James Meiss")

0.11 -

[Andrew B Frigyik](http://www.scholarpedia.org/article/User:Andrew_B_Frigyik "User:Andrew B Frigyik")

0.11 -

[Tobias Denninger](http://www.scholarpedia.org/article/User:Tobias_Denninger "User:Tobias Denninger")

[Ludwig Arnold](http://www.scholarpedia.org/article/User:Ludwig_Arnold "User:Ludwig Arnold")

*   [Dr. Valery Oseledets, Lomonosov Moscow State University, Russia](http://www.scholarpedia.org/article/User:Valery_Oseledets "User:Valery Oseledets")
    

Contents
--------

 \[[hide](http://www.scholarpedia.org/article/Oseledets_theorem#)\
\] 

*   [1 Introduction](http://www.scholarpedia.org/article/Oseledets_theorem#Introduction)
    
*   [2 Oseledets' Multiplicative Ergodic Theorem](http://www.scholarpedia.org/article/Oseledets_theorem#Oseledets.27_Multiplicative_Ergodic_Theorem)
    
*   [3 The case of invertible transformations](http://www.scholarpedia.org/article/Oseledets_theorem#The_case_of_invertible_transformations)
    
*   [4 The continuous-time case](http://www.scholarpedia.org/article/Oseledets_theorem#The_continuous-time_case)
    
*   [5 History](http://www.scholarpedia.org/article/Oseledets_theorem#History)
    
*   [6 Acknowledgments](http://www.scholarpedia.org/article/Oseledets_theorem#Acknowledgments)
    
*   [7 References](http://www.scholarpedia.org/article/Oseledets_theorem#References)
    
*   [8 See Also](http://www.scholarpedia.org/article/Oseledets_theorem#See_Also)
    

Introduction
------------

Let A0,A1,...,At,... be a sequence of nonsingular m×mmatrices satisfying 1tlog||At||→0, and let A(t)\=At−1⋯A0 for t\=1,2,... . Suppose there is a number c\>0 such that ||A(t)||≤exp(ct) . The [Lyapunov exponent](http://www.scholarpedia.org/article/Lyapunov_exponent "Lyapunov exponent")
 of a nonzero vector e∈Rm is defined by

χ(e)\=lim sup1tlog||A(t)e||.(1)

More generally, let ek be a subspace ofRm of dimension k and λ(t,ek) the absolute value of the determinant of the linear transformation ek→A(t)ek defined by the matrix A(t) . In particular, λ(t,e1)\=||A(t)e||||e|| for a nonzero vector e∈e1 . The Lyapunov exponent of the subspace is defined by χ(ek)\=lim sup1tlogλ(t,ek) . This reduces to the definition ([1](http://www.scholarpedia.org/article/Oseledets_theorem#Eq-1)
) for the one-dimensional case.

The function χ(e) attains at most m distinct values χ1<χ2<..<χr for some r≤m . Let Li be the subspace defined by the condition χ(e)≤χi,0≠e∈Li. We have that L0\=0⊂L1⊂....⊂Lr\=Rm and that χ(e)\=χi for 0≠e∈Li∖Li−1,i\=1,..r.The number ki\=dim(Li)−dim(Li−1) is called the multiplicity of the value χi . The sequence A(t) is said to be **Lyapunov regular** if

∑i\=1rkiχi\=lim1tlog|detA(t)|.

**Theorem 1.** If the sequence A(t) is Lyapunov regular, then the [Lyapunov exponents](http://www.scholarpedia.org/article/Attractor_Dimensions "Attractor Dimensions")
 of all orders are exact, i.e., χ(ek)\=lim1tlogλ(t,ek).

Denote the transpose of the matrix A by A∗ .

**Theorem 2.** If the sequence A(t) is Lyapunov regular, then the following is true : i) lim(A∗(t)A(t))12t\=Λ where Λ is a diagonal matrix; ii) exp(χ1),...,exp(χr) are the distinct eigenvalues of Λ and ki the multiplicity of exp(χi); iii) lim1tlog||A(t)Λ−t||\=0.

Oseledets' Multiplicative Ergodic Theorem
-----------------------------------------

Let T be a measure preserving transformation of a probability Lebesgue space (X,Σ,μ) and A(t,x)\=A(Tt−1x)...A(x) , where A:X→Gl(m,R) is a measurable map satisfying log+||A(x)||∈L1(X,μ).

**Theorem 3.** The function t→A(t,x) is Lyapunov regular for μ\-almost every x . The function Λ\=Λ(x) is measurable. The filtration L1(x)⊂....⊂Lr(x)\=Rm is measurable.

The case of invertible transformations
--------------------------------------

Let T and T−1 be measure preserving transformations. Assume that log+||A(x)|| and log+||A−1(x)|| are integrable. Let A(t,x)\=A−1(Ttx)...A−1(T−1x),t≤−1.

**Theorem 4.** The function t→A(t,x) is Lyapunov regular as t→±∞ forμ\-almost every x . There is a measurable splitting Rm\=Ek1(x)⊕...⊕Ekr(x)such that limt→±∞1tlog||A(t,x)e||\=χi(x) for 0≠e∈Eki(x) and dim(Eki(x))\=ki(x). If ek⊂Eki(x) then limt→±∞1tlogλ(ek)\=kχi(x) uniformly over ek⊂Eki(x). Furthermore, limt→±∞1tlogsin(∠(Eki(Ttx),Ekj(Ttx))\=0,i≠j and χi(Tx)\=χ(x),ki(Tx)\=ki(x),Eki(Tx)(Tx)\=A(x)Eki(x)(x). The subspaces Eki(x) are called Oseledets subspaces.

The continuous-time case
------------------------

A(t,x) is called a cocycle if A(t+s,x)\=A(t,Tsx)A(s,x), where A:R×X→GL(m,R) is a measurable function and {Tt} is a measurable measure preserving flow in a probability Lebesgue space (X,Σ,μ) : Tt+s\=TtTs . Let sup{log+||A(t,x)||:−1≤t≤1} be integrable. The statements such as in theorems 3,4 are also true in the continuous-time case. The derivatives of deterministic and stochastic flows provide examples of such cocycles.

History
-------

In 1965 the author of this paper was a graduate student. His scientific adviser was Y. Sinai. From Sinai's work it became clear that the positive [entropy](http://www.scholarpedia.org/article/Entropy "Entropy")
 in the classical [dynamical systems](http://www.scholarpedia.org/article/Dynamical_systems "Dynamical systems")
 is related to exponential divergence of orbits originating at nearby points. This connection became the starting point of the author's interest in the problem of exponential divergence. In 1965, during the workshop on ergodic theory in Khumsan, author proved the multiplicative ergodic theorem (MET). The main idea of the proof of the MET is to reduce the general case to the case of triangular cocycles. In 1966 the author gave a talk entitled "The strong law of large numbers for random matrix processes" at the International Congress of Mathematicians in Moscow. A year later the author defended his Ph.D. thesis; the third chapter of this thesis was called "A multiplicative ergodic theorem. Lyapunov characteristic numbers for dynamical systems". Finally, in 1968 the paper with the same title was published. Raghunathan gave another proof of the MET. It exploits Kingman's subadditive ergodic theorem. V.A. Kaimanovich proved a MET for semisimple Lie groups. Ruelle extended the MET to the case of Hilbert spaces and Mane extended it to the case of Banach spaces. Following V.A. Kaimanovich, A.Karlsson and G.Margulis obtained an extension of the MET to some nonpositively curved spaces. A.Karlsson and F.Ledrappier proved a MET for the group ISO(X) of a proper metric space X. Duchin proved a MET for the mapping class groups. You can find more details in the books by L. Arnold, by U. Krengel and by L. Barreira and Ya. Pesin for a description of various versions of the MET.

Acknowledgments
---------------

The author's research on the MET was partially supported by RFBR Grant 07-01-00203.

References
----------

*   A.M. Lyapunov, The general problem of the [stability](http://www.scholarpedia.org/article/Stability "Stability")
     of motion, Taylor & Francis, 1992.
*   V.I. Oseledets, A multiplicative ergodic theorem. Lyapunov characteristic numbers for dynamical systems, Trans. Moscow Math. Soc. 19 (1968), 197-231. Moscov.Mat.Obsch.19 (1968), 179-210.
*   M.S. Raghunathan, A proof of Oseledec's multiplicative ergodic theorem, Israel JM 32 (1979), 365-362.
*   D Ruelle, Ergodic theory of differentiable dynamical systems, Inst.des Hautes Etudes Scient., Publ. Math.50 (1979), 275-306.
*   R. Mane, Lyapunov exponents and stable manifolds for compact transformations, Geometric dynamics,Lecture Notes in Math.1007, Springer (1983), 522-577.
*   L. Arnold, Random dynamical systems, Monographs in Mathematics, Springer, 1998.
*   U. Krengel, Ergodic theorems, Walter de Gruyter, Berlin New York, 1985.
*   L. Barreira and Ya. Pesin, [Nonuniform hyperbolicity](http://www.scholarpedia.org/article/Nonuniform_hyperbolicity "Nonuniform hyperbolicity")
    : dynamics of systems with nonzero Lyapunov exponents, Encyclopedia of Mathematics and its Applications, Cambridge University Press, 2007
*   A. Karlsson and G.Margulis, A multiplicative ergodic theorem and nonpositive curved spaces, Comm.Math.Phys. 22 (1999), 107-123.
*   V.A. Kaimanovich, Lyapunov exponents, symmetric spaces and a multiplicative ergodic theorem for semisimple Lie groups, J. Soviet Math. 47 (1989), 2387-2398.
*   A. Karlsson and F. Leddrapier, On laws of large numbers for random walks, Annals of Probability 34 (2006), 1693-1706.
*   M. Duchin, The thin triangles and a multiplicative ergodic theorem for Teichmuller geometry (2005), arXiv: math/0508046.

**Internal references**

*   Edward Ott (2008) [Attractor dimensions](http://www.scholarpedia.org/article/Attractor_dimensions "Attractor dimensions")
    . [Scholarpedia](http://www.scholarpedia.org/article/Scholarpedia "Scholarpedia")
    , 3(3):2110.

*   James Meiss (2007) [Dynamical systems](http://www.scholarpedia.org/article/Dynamical_systems "Dynamical systems")
    . Scholarpedia, 2(2):1629.

*   Tomasz Downarowicz (2007) [Entropy](http://www.scholarpedia.org/article/Entropy "Entropy")
    . Scholarpedia, 2(11):3901.

*   Yakov Pesin and Boris Hasselblatt (2008) [Nonuniform hyperbolicity](http://www.scholarpedia.org/article/Nonuniform_hyperbolicity "Nonuniform hyperbolicity")
    . Scholarpedia, 3(1):4842.

*   Boris Hasselblatt and Yakov Pesin (2008) [Pesin entropy formula](http://www.scholarpedia.org/article/Pesin_entropy_formula "Pesin entropy formula")
    . Scholarpedia, 3(3):3733.

  

See Also
--------

[Dynamical Systems](http://www.scholarpedia.org/article/Dynamical_Systems "Dynamical Systems")
, [Entropy](http://www.scholarpedia.org/article/Entropy "Entropy")
, [Ergodic Theory](http://www.scholarpedia.org/w/index.php?title=Ergodic_Theory&action=edit&redlink=1 "Ergodic Theory (page does not exist)")
, [Invariant Measures](http://www.scholarpedia.org/w/index.php?title=Invariant_Measures&action=edit&redlink=1 "Invariant Measures (page does not exist)")
, [Nonuniform Hyperbolicity](http://www.scholarpedia.org/article/Nonuniform_Hyperbolicity "Nonuniform Hyperbolicity")
, [Partial Hyperbolicity](http://www.scholarpedia.org/article/Partial_Hyperbolicity "Partial Hyperbolicity")
, [Pesin Entropy Formula](http://www.scholarpedia.org/article/Pesin_Entropy_Formula "Pesin Entropy Formula")

|     |
| --- |
| Sponsored by: [Eugene M. Izhikevich, Editor-in-Chief of Scholarpedia, the peer-reviewed open-access encyclopedia](http://www.scholarpedia.org/article/User:Eugene_M._Izhikevich "User:Eugene M. Izhikevich") |
| [Reviewed by](http://www.scholarpedia.org/w/index.php?title=Oseledets_theorem&oldid=25623)<br>: [Anonymous](http://www.scholarpedia.org/article/User:Anonymous "User:Anonymous") |
| [Reviewed by](http://www.scholarpedia.org/w/index.php?title=Oseledets_theorem&oldid=25872)<br>: [Dr. Ludwig Arnold, Mathematics, University of Bremen, Germany](http://www.scholarpedia.org/article/User:Ludwig_Arnold "User:Ludwig Arnold") |
| Accepted on: [2007-11-21 16:35:31 GMT](http://www.scholarpedia.org/w/index.php?title=Oseledets_theorem&oldid=25877) |

Retrieved from "[http://www.scholarpedia.org/w/index.php?title=Oseledets\_theorem&oldid=142085](http://www.scholarpedia.org/w/index.php?title=Oseledets_theorem&oldid=142085)
"

[Categories](http://www.scholarpedia.org/article/Special:Categories "Special:Categories")
:

*   [Dynamical Systems](http://www.scholarpedia.org/article/Category:Dynamical_Systems "Category:Dynamical Systems")
    
*   [Ergodic Theory](http://www.scholarpedia.org/article/Category:Ergodic_Theory "Category:Ergodic Theory")
    
*   [Eponymous](http://www.scholarpedia.org/article/Category:Eponymous "Category:Eponymous")
    

##### Personal tools

*   [Log in](http://www.scholarpedia.org/w/index.php?title=Special:UserLogin&returnto=Oseledets+theorem "You are encouraged to log in; however, it is not mandatory [alt-o]")
    

##### Namespaces

*   [Page](http://www.scholarpedia.org/article/Oseledets_theorem "View the content page [alt-c]")
    
*   [Discussion](http://www.scholarpedia.org/w/index.php?title=Talk:Oseledets_theorem&action=edit&redlink=1 "Discussion about the content page [alt-t]")
    

##### Variants[](http://www.scholarpedia.org/article/Oseledets_theorem#)

##### Views

*   [Read](http://www.scholarpedia.org/article/Oseledets_theorem)
    
*   [View source](http://www.scholarpedia.org/w/index.php?title=Oseledets_theorem&action=edit "This page is protected.
    You can view its source [alt-e]")
    
*   [View history](http://www.scholarpedia.org/w/index.php?title=Oseledets_theorem&action=history "Past revisions of this page [alt-h]")
    

##### Actions[](http://www.scholarpedia.org/article/Oseledets_theorem#)

##### Search

 ![Search](http://www.scholarpedia.org/w/skins/vector/images/search-ltr.png?303) 

[](http://www.scholarpedia.org/article/Main_Page "Visit the main page")

##### Navigation

*   [Main page](http://www.scholarpedia.org/article/Main_Page "Visit the main page [alt-z]")
    
*   [About](http://www.scholarpedia.org/article/Scholarpedia:About)
    
*   [Propose a new article](http://www.scholarpedia.org/article/Special:ProposeArticle)
    
*   [Instructions for Authors](http://www.scholarpedia.org/article/Scholarpedia:Instructions_for_Authors)
    
*   [Random article](http://www.scholarpedia.org/article/Special:Random "Load a random page [alt-x]")
    
*   [FAQs](http://www.scholarpedia.org/article/Help:Frequently_Asked_Questions)
    
*   [Help](http://www.scholarpedia.org/article/Scholarpedia:Help)
    

##### Focal areas

*   [Astrophysics](http://www.scholarpedia.org/article/Encyclopedia:Astrophysics)
    
*   [Celestial mechanics](http://www.scholarpedia.org/article/Encyclopedia:Celestial_Mechanics)
    
*   [Computational neuroscience](http://www.scholarpedia.org/article/Encyclopedia:Computational_neuroscience)
    
*   [Computational intelligence](http://www.scholarpedia.org/article/Encyclopedia:Computational_intelligence)
    
*   [Dynamical systems](http://www.scholarpedia.org/article/Encyclopedia:Dynamical_systems)
    
*   [Physics](http://www.scholarpedia.org/article/Encyclopedia:Physics)
    
*   [Touch](http://www.scholarpedia.org/article/Encyclopedia:Touch)
    
*   [More topics](http://www.scholarpedia.org/article/Scholarpedia:Topics)
    

##### Activity

*   [Recently published articles](http://www.scholarpedia.org/article/Special:RecentlyPublished)
    
*   [Recently sponsored articles](http://www.scholarpedia.org/article/Special:RecentlySponsored)
    
*   [Recent changes](http://www.scholarpedia.org/article/Special:RecentChanges "A list of recent changes in the wiki [alt-r]")
    
*   [All articles](http://www.scholarpedia.org/article/Special:AllPages)
    
*   [List all Curators](http://www.scholarpedia.org/article/Special:ListCurators)
    
*   [List all users](http://www.scholarpedia.org/article/Special:ListUsers)
    
*   [Scholarpedia Journal](http://www.scholarpedia.org/article/Special:Journal)
    

##### Tools

*   [What links here](http://www.scholarpedia.org/article/Special:WhatLinksHere/Oseledets_theorem "A list of all wiki pages that link here [alt-j]")
    
*   [Related changes](http://www.scholarpedia.org/article/Special:RecentChangesLinked/Oseledets_theorem "Recent changes in pages linked from this page [alt-k]")
    
*   [Special pages](http://www.scholarpedia.org/article/Special:SpecialPages "A list of all special pages [alt-q]")
    
*   [Printable version](http://www.scholarpedia.org/w/index.php?title=Oseledets_theorem&printable=yes)
    
*   [Permanent link](http://www.scholarpedia.org/w/index.php?title=Oseledets_theorem&oldid=142085 "Permanent link to this revision of the page")
    

*   [![](http://www.scholarpedia.org/w/skins/vector/images/twitter.png?303)](https://twitter.com/scholarpedia)
    
*   [![](https://ssl.gstatic.com/images/icons/gplus-16.png)](https://plus.google.com/112873162496270574424)
    
*   [![](http://www.scholarpedia.org/w/skins/vector/images/facebook.png?303)](http://www.facebook.com/Scholarpedia)
    
*   [![](http://www.scholarpedia.org/w/skins/vector/images/linkedin.png?303)](http://www.linkedin.com/groups/Scholarpedia-4647975/about)
    

*   [![Powered by MediaWiki](http://www.scholarpedia.org/w/skins/common/images/poweredby_mediawiki_88x31.png)](https://www.mediawiki.org/)
     [![Powered by MathJax](http://www.scholarpedia.org/w/skins/common/images/MathJaxBadge.gif)](https://www.mathjax.org/)
     [![Creative Commons License](http://www.scholarpedia.org/w/skins/common/88x31.png)](http://creativecommons.org/licenses/by-nc-sa/3.0/deed.en_US)
    

*   This page was last modified on 22 June 2014, at 08:36.
*   This page has been accessed 121,465 times.
*   "Oseledets theorem" by [Valery Oseledets](http://www.scholarpedia.org/article/Oseledets_theorem)
     is licensed under a [Creative Commons Attribution-NonCommercial-ShareAlike 3.0 Unported License](http://creativecommons.org/licenses/by-nc-sa/3.0/deed.en_US)
    . Permissions beyond the scope of this license are described in the [Terms of Use](http://www.scholarpedia.org/article/Scholarpedia:Terms_of_use)
    

*   [Privacy policy](http://www.scholarpedia.org/article/Scholarpedia:Privacy_policy "Scholarpedia:Privacy policy")
    
*   [About Scholarpedia](http://www.scholarpedia.org/article/Scholarpedia:About "Scholarpedia:About")
    
*   [Disclaimers](http://www.scholarpedia.org/article/Scholarpedia:General_disclaimer "Scholarpedia:General disclaimer")
    

