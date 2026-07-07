![Wikipedia App Icon](https://upload.wikimedia.org/wikipedia/donate/thumb/b/bf/Phonebaby.png/250px-Phonebaby.png)

Did you know that Wikipedia has an app?

**Download it now and save articles to read offline**

Install

[](https://en.wikipedia.org/wiki/Oseledets_theorem#)

*   [Home](https://en.wikipedia.org/wiki/Main_Page)
    
*   [Random](https://en.wikipedia.org/wiki/Special:Random)
    
*   [Nearby](https://en.wikipedia.org/wiki/Special:Nearby)
    

*   [Log in](https://en.wikipedia.org/w/index.php?title=Special%3AUserLogin&returnto=Oseledets+theorem&experiments=we-1-8-account-creation-form-v2%3Aunsampled)
    

*   [Settings](https://en.wikipedia.org/w/index.php?title=Special:MobileOptions&returnto=Oseledets+theorem)
    

[Donate Now If Wikipedia is useful to you, please give today.\
\
 ![](https://en.wikipedia.org/static/images/donate/donate.gif)](https://donate.wikimedia.org/?wmf_source=donate&wmf_medium=sidebar&wmf_campaign=en.wikipedia.org&uselang=en&wmf_key=minerva)
 

*   [About Wikipedia](https://en.wikipedia.org/wiki/Wikipedia:About)
    
*   [Disclaimers](https://en.wikipedia.org/wiki/Wikipedia:General_disclaimer)
    

[![Wikipedia](https://en.wikipedia.org/static/images/mobile/copyright/wikipedia-wordmark-en-25.svg)](https://en.wikipedia.org/wiki/Main_Page)

 

Search

Oseledets theorem
=================

*   [Article](https://en.wikipedia.org/wiki/Oseledets_theorem)
    
*   [Talk](https://en.wikipedia.org/wiki/Talk:Oseledets_theorem)
    

*   [Language](https://en.wikipedia.org/wiki/Oseledets_theorem#p-lang "Language")
    
*   [Loading… Download PDF](https://en.wikipedia.org/wiki/Oseledets_theorem# "Download PDF [alt-p]")
    
*   [Watch](https://en.wikipedia.org/w/index.php?title=Special%3AUserLogin&returnto=Oseledets+theorem&experiments=we-1-8-account-creation-form-v2%3Aunsampled)
    
*   [Edit](https://en.wikipedia.org/w/index.php?title=Oseledets_theorem&action=edit&section=0)
    

For non-technical introduction to [ergodicity](https://en.wikipedia.org/wiki/Ergodicity "Ergodicity")
, see [ergodic hypothesis](https://en.wikipedia.org/wiki/Ergodic_hypothesis "Ergodic hypothesis")
.

In [mathematics](https://en.wikipedia.org/wiki/Mathematics "Mathematics")
, the **multiplicative ergodic theorem**, or **Oseledets theorem** provides the theoretical background for computation of [Lyapunov exponents](https://en.wikipedia.org/wiki/Lyapunov_exponent "Lyapunov exponent")
 of a [nonlinear](https://en.wikipedia.org/wiki/Nonlinear_system "Nonlinear system")
 [dynamical system](https://en.wikipedia.org/wiki/Dynamical_system "Dynamical system")
. It was proved by [Valery Oseledets](https://en.wikipedia.org/wiki/Valeriy_Oseledets "Valeriy Oseledets")
 (also spelled "Oseledec") in 1965 and reported at the [International Mathematical Congress](https://en.wikipedia.org/wiki/International_Mathematical_Congress "International Mathematical Congress")
 in Moscow in 1966. A conceptually different proof of the multiplicative [ergodic theorem](https://en.wikipedia.org/wiki/Ergodic_theorem "Ergodic theorem")
 was found by [M. S. Raghunathan](https://en.wikipedia.org/wiki/M._S._Raghunathan "M. S. Raghunathan")
.\[_[citation needed](https://en.wikipedia.org/wiki/Wikipedia:Citation_needed "Wikipedia:Citation needed")\
_\][\[1\]](https://en.wikipedia.org/wiki/Oseledets_theorem#cite_note-1)
 The theorem has been extended to [semisimple Lie groups](https://en.wikipedia.org/wiki/Semisimple_Lie_group "Semisimple Lie group")
 by V. A. Kaimanovich and further generalized in the works of [David Ruelle](https://en.wikipedia.org/wiki/David_Ruelle "David Ruelle")
, [Grigory Margulis](https://en.wikipedia.org/wiki/Grigory_Margulis "Grigory Margulis")
, [Anders Karlsson](https://en.wikipedia.org/wiki/Anders_Karlsson_(mathematician) "Anders Karlsson (mathematician)")
, and [François Ledrappier](https://en.wikipedia.org/wiki/Fran%C3%A7ois_Ledrappier "François Ledrappier")
.\[_[citation needed](https://en.wikipedia.org/wiki/Wikipedia:Citation_needed "Wikipedia:Citation needed")\
_\]

Contents
--------

*   [1 Cocycles](https://en.wikipedia.org/wiki/Oseledets_theorem#Cocycles)
    *   [1.1 Examples](https://en.wikipedia.org/wiki/Oseledets_theorem#Examples)
        
*   [2 Statement of the theorem](https://en.wikipedia.org/wiki/Oseledets_theorem#Statement_of_the_theorem)
    
*   [3 Additive versus multiplicative ergodic theorems](https://en.wikipedia.org/wiki/Oseledets_theorem#Additive_versus_multiplicative_ergodic_theorems)
    
*   [4 References](https://en.wikipedia.org/wiki/Oseledets_theorem#References)
    
*   [5 External links](https://en.wikipedia.org/wiki/Oseledets_theorem#External_links)
    

Cocycles
--------

[edit](https://en.wikipedia.org/w/index.php?title=Oseledets_theorem&action=edit&section=1 "Edit section: Cocycles")

The multiplicative ergodic theorem is stated in terms of matrix cocycles of a dynamical system. The theorem states conditions for the existence of the defining limits and describes the Lyapunov exponents. It does not address the rate of convergence.

A **cocycle** of an autonomous dynamical system _X_ is a map _C_ : _X×T_ → **R**_n×n_ satisfying

C ( x , 0 ) \= I n   f o r   a l l   x ∈ X {\\displaystyle C(x,0)=I\_{n}{\\rm {~for~all~}}x\\in X} ![{\displaystyle C(x,0)=I_{n}{\rm {~for~all~}}x\in X}](https://wikimedia.org/api/rest_v1/media/math/render/svg/c9e112874712ac7a5921fdbedd0a0a403e953711) 

C ( x , t + s ) \= C ( x ( t ) , s ) C ( x , t )   f o r   a l l   x ∈ X   a n d   t , s ∈ T {\\displaystyle C(x,t+s)=C(x(t),s)\\,C(x,t){\\rm {~for~all~}}x\\in X{\\rm {~and~}}t,s\\in T} ![{\displaystyle C(x,t+s)=C(x(t),s)\,C(x,t){\rm {~for~all~}}x\in X{\rm {~and~}}t,s\in T}](https://wikimedia.org/api/rest_v1/media/math/render/svg/ce204d993bde6ca9c612ab9eaa2666f63fc62e59) 

where _X_ and _T_ (with _T_ = **Z⁺** or _T_ = **R⁺**) are the phase space and the time range, respectively, of the dynamical system, and _I__n_ is the _n_\-dimensional unit matrix. The dimension _n_ of the matrices _C_ is not related to the phase space _X_.

### Examples

[edit](https://en.wikipedia.org/w/index.php?title=Oseledets_theorem&action=edit&section=2 "Edit section: Examples")

*   A prominent example of a cocycle is given by the matrix _J__t_ in the theory of Lyapunov exponents. In this special case, the dimension _n_ of the matrices is the same as the dimension of the manifold _X_.
*   For any cocycle _C_, the [determinant](https://en.wikipedia.org/wiki/Determinant "Determinant")
     det _C_(_x_, _t_) is a one-dimensional cocycle.

Statement of the theorem
------------------------

[edit](https://en.wikipedia.org/w/index.php?title=Oseledets_theorem&action=edit&section=3 "Edit section: Statement of the theorem")

Let _μ_ be an ergodic invariant measure on _X_ and _C_ a cocycle of the dynamical system such that for each _t_ ∈ _T_, the maps x → log ⁡ ‖ C ( x , t ) ‖ {\\displaystyle x\\rightarrow \\log \\|C(x,t)\\|} ![{\displaystyle x\rightarrow \log \|C(x,t)\|}](https://wikimedia.org/api/rest_v1/media/math/render/svg/75821e2673f5db6f022f343469522ed8da57c781) and x → log ⁡ ‖ C ( x , t ) − 1 ‖ {\\displaystyle x\\rightarrow \\log \\|C(x,t)^{-1}\\|} ![{\displaystyle x\rightarrow \log \|C(x,t)^{-1}\|}](https://wikimedia.org/api/rest_v1/media/math/render/svg/a5c7913ec8752ef512eb40f6e1a358112127d4b6) are _L_1\-integrable with respect to _μ_. Then for _μ_\-almost all _x_ and each non-zero vector _u_ ∈ **R**_n_ the limit

λ \= lim t → ∞ 1 t log ⁡ ‖ C ( x , t ) u ‖ ‖ u ‖ {\\displaystyle \\lambda =\\lim \_{t\\to \\infty }{1 \\over t}\\log {\\|C(x,t)u\\| \\over \\|u\\|}} ![{\displaystyle \lambda =\lim _{t\to \infty }{1 \over t}\log {\|C(x,t)u\| \over \|u\|}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/6792375925b25e20eaa39412370303aae80053c8) 

exists and assumes, depending on _u_ but not on _x_, up to _n_ different values. These are the Lyapunov exponents.

Further, if _λ_1 > ... > _λ__m_ are the different limits then there are subspaces **R**_n_ = _R_1 ⊃ ... ⊃ _R__m_ ⊃ _R__m_+1 = {0}, depending on _x_, such that the limit is _λ__i_ for _u_ ∈ _R__i_ \\ _R__i_+1 and _i_ \= 1, ..., _m_.

The values of the Lyapunov exponents are invariant with respect to a wide range of coordinate transformations. Suppose that _g_ : _X_ → _X_ is a one-to-one map such that ∂ g / ∂ x {\\displaystyle \\partial g/\\partial x} ![{\displaystyle \partial g/\partial x}](https://wikimedia.org/api/rest_v1/media/math/render/svg/79ec72c405a9a2d2d676e3117bf3284e15b1d518) and its inverse exist; then the values of the Lyapunov exponents do not change.

Additive versus multiplicative ergodic theorems
-----------------------------------------------

[edit](https://en.wikipedia.org/w/index.php?title=Oseledets_theorem&action=edit&section=4 "Edit section: Additive versus multiplicative ergodic theorems")

Verbally, ergodicity means that time and space averages are equal, formally:

lim t → ∞ 1 t ∫ 0 t f ( x ( s ) ) d s \= 1 μ ( X ) ∫ X f ( x ) μ ( d x ) {\\displaystyle \\lim \_{t\\to \\infty }{1 \\over t}\\int \_{0}^{t}f(x(s))\\,ds={1 \\over \\mu (X)}\\int \_{X}f(x)\\,\\mu (dx)} ![{\displaystyle \lim _{t\to \infty }{1 \over t}\int _{0}^{t}f(x(s))\,ds={1 \over \mu (X)}\int _{X}f(x)\,\mu (dx)}](https://wikimedia.org/api/rest_v1/media/math/render/svg/08542ee10da8f9e7e7282b20c73a3ba005543d22) 

where the integrals and the limit exist. Space average (right hand side, μ is an ergodic measure on _X_) is the accumulation of _f_(_x_) values weighted by μ(_dx_). Since addition is commutative, the accumulation of the _f_(_x_)μ(_dx_) values may be done in arbitrary order. In contrast, the time average (left hand side) suggests a specific ordering of the _f_(_x_(_s_)) values along the trajectory.

Since matrix multiplication is, in general, not commutative, accumulation of multiplied cocycle values (and limits thereof) according to _C_(_x_(_t_0),_t__k_) = _C_(_x_(_t__k_−1),_t__k_ − _t__k_−1) ... _C_(_x_(_t_0),_t_1 − _t_0) — for _t__k_ large and the steps _t__i_ − _t__i_−1 small — makes sense only for a prescribed ordering. Thus, the time average may exist (and the theorem states that it actually exists), but there is no space average counterpart. In other words, the Oseledets theorem differs from additive ergodic theorems (such as [G. D. Birkhoff](https://en.wikipedia.org/wiki/G._D._Birkhoff "G. D. Birkhoff")
's and [J. von Neumann](https://en.wikipedia.org/wiki/J._von_Neumann "J. von Neumann")
's) in that it guarantees the existence of the time average, but makes no claim about the space average.

References
----------

[edit](https://en.wikipedia.org/w/index.php?title=Oseledets_theorem&action=edit&section=5 "Edit section: References")

1.  [↑](https://en.wikipedia.org/wiki/Oseledets_theorem#cite_ref-1 "Jump up")
     ["Oseledets' multiplicative ergodic theorem and Lyapunov exponents"](https://people.maths.bris.ac.uk/~macpd/ads/oseledets.pdf)
     (PDF).

*   Oseledets, V. I. (1968). "Мультипликативная эргодическая теорема. Характеристические показатели Ляпунова динамических систем" \[Multiplicative ergodic theorem: Characteristic Lyapunov exponents of dynamical systems\]. _Trudy MMO_ (in Russian). **19**: 179–210.
*   Ruelle, D. (1979). ["Ergodic theory of differentiable dynamic systems"](http://www.numdam.org/article/PMIHES_1979__50__27_0.pdf)
     (PDF). _IHES Publ. Math_. **50** (1): 27–58\. [doi](https://en.wikipedia.org/wiki/Doi_(identifier) "Doi (identifier)")
    :[10.1007/BF02684768](https://doi.org/10.1007%2FBF02684768)
    . [S2CID](https://en.wikipedia.org/wiki/S2CID_(identifier) "S2CID (identifier)")
     [56389695](https://api.semanticscholar.org/CorpusID:56389695)
    .

External links
--------------

[edit](https://en.wikipedia.org/w/index.php?title=Oseledets_theorem&action=edit&section=6 "Edit section: External links")

*   V. I. Oseledets, [_Oseledets theorem_](http://www.scholarpedia.org/article/Oseledets_theorem)
     at [Scholarpedia](https://en.wikipedia.org/wiki/Scholarpedia "Scholarpedia")
    

 

Retrieved from "[https://en.wikipedia.org/w/index.php?title=Oseledets\_theorem&oldid=1286205727](https://en.wikipedia.org/w/index.php?title=Oseledets_theorem&oldid=1286205727)
"

[**Last edited 1 year ago** by SpiralSource](https://en.wikipedia.org/w/index.php?title=Oseledets_theorem&action=history)

#### Languages

*   [Deutsch](https://de.wikipedia.org/wiki/Multiplikativer_Ergodensatz "Multiplikativer Ergodensatz – German")
    
*   [Русский](https://ru.wikipedia.org/wiki/%D0%A2%D0%B5%D0%BE%D1%80%D0%B5%D0%BC%D0%B0_%D0%9E%D1%81%D0%B5%D0%BB%D0%B5%D0%B4%D1%86%D0%B0 "Теорема Оселедца – Russian")
    

![Wikipedia](https://en.wikipedia.org/static/images/mobile/copyright/wikipedia-wordmark-en-25.svg)

*   [![Wikimedia Foundation](https://en.wikipedia.org/static/images/footer/wikimedia.svg)](https://www.wikimedia.org/)
    
*   [![Powered by MediaWiki](https://en.wikipedia.org/w/resources/assets/mediawiki_compact.svg)](https://www.mediawiki.org/)
    

*   This page was last edited on 18 April 2025, at 11:51 (UTC).
*   Page was rendered with [Parsoid](https://www.mediawiki.org/wiki/Special:MyLanguage/Parsoid "mw:Special:MyLanguage/Parsoid")
    .
*   Content is available under [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/deed.en)
     unless otherwise noted.

*   [Privacy policy](https://foundation.wikimedia.org/wiki/Special:MyLanguage/Policy:Privacy_policy)
    
*   [About Wikipedia](https://en.wikipedia.org/wiki/Wikipedia:About)
    
*   [Disclaimers](https://en.wikipedia.org/wiki/Wikipedia:General_disclaimer)
    
*   [Contact Wikipedia](https://en.wikipedia.org/wiki/Wikipedia:Contact_us)
    
*   [Legal & safety contacts](https://foundation.wikimedia.org/wiki/Special:MyLanguage/Legal:Wikimedia_Foundation_Legal_and_Safety_Contact_Information)
    
*   [Code of Conduct](https://foundation.wikimedia.org/wiki/Special:MyLanguage/Policy:Universal_Code_of_Conduct)
    
*   [Developers](https://developer.wikimedia.org/)
    
*   [Statistics](https://stats.wikimedia.org/#/en.wikipedia.org)
    
*   [Cookie statement](https://foundation.wikimedia.org/wiki/Special:MyLanguage/Policy:Cookie_statement)
    
*   [Terms of Use](https://foundation.m.wikimedia.org/wiki/Special:MyLanguage/Policy:Terms_of_Use)
    
*   [Desktop view](https://en.wikipedia.org/w/index.php?title=Oseledets_theorem&mobileaction=toggle_view_desktop)
    
*   [Edit preview settings](https://en.wikipedia.org/wiki/Oseledets_theorem#)