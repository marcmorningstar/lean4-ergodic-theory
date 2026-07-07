[](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#)

*   [Home](https://en.wikipedia.org/wiki/Main_Page)
    
*   [Random](https://en.wikipedia.org/wiki/Special:Random)
    
*   [Nearby](https://en.wikipedia.org/wiki/Special:Nearby)
    

*   [Log in](https://en.wikipedia.org/w/index.php?title=Special%3AUserLogin&returnto=Kingman%27s+subadditive+ergodic+theorem&experiments=we-1-8-account-creation-form-v2%3Aunsampled)
    

*   [Settings](https://en.wikipedia.org/w/index.php?title=Special:MobileOptions&returnto=Kingman%27s+subadditive+ergodic+theorem)
    

[Donate Now If Wikipedia is useful to you, please give today.\
\
 ![](https://en.wikipedia.org/static/images/donate/donate.gif)](https://donate.wikimedia.org/?wmf_source=donate&wmf_medium=sidebar&wmf_campaign=en.wikipedia.org&uselang=en&wmf_key=minerva)
 

*   [About Wikipedia](https://en.wikipedia.org/wiki/Wikipedia:About)
    
*   [Disclaimers](https://en.wikipedia.org/wiki/Wikipedia:General_disclaimer)
    

[![Wikipedia](https://en.wikipedia.org/static/images/mobile/copyright/wikipedia-wordmark-en-25.svg)](https://en.wikipedia.org/wiki/Main_Page)

 

Search

Kingman's subadditive ergodic theorem
=====================================

*   [Article](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem)
    
*   [Talk](https://en.wikipedia.org/wiki/Talk:Kingman%27s_subadditive_ergodic_theorem)
    

*   [Language](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem "Language")
    
*   [Watch](https://en.wikipedia.org/w/index.php?title=Special%3AUserLogin&returnto=Kingman%27s+subadditive+ergodic+theorem&experiments=we-1-8-account-creation-form-v2%3Aunsampled)
    
*   [Edit](https://en.wikipedia.org/w/index.php?title=Kingman%27s_subadditive_ergodic_theorem&action=edit)
    

In mathematics, **Kingman's subadditive ergodic theorem** is one of several [ergodic theorems](https://en.wikipedia.org/wiki/Ergodic_theory#Ergodic_theorems "Ergodic theory")
. It can be seen as a generalization of [Birkhoff's ergodic theorem](https://en.wikipedia.org/wiki/Ergodic_theory#Ergodic_theorems "Ergodic theory")
.[\[1\]](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#cite_note-proof1-1)
 Intuitively, the subadditive ergodic theorem is a kind of [random variable](https://en.wikipedia.org/wiki/Random_variable "Random variable")
 version of [Fekete's lemma](https://en.wikipedia.org/wiki/Subadditivity#Properties "Subadditivity")
 (hence the name ergodic).[\[2\]](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#cite_note-2)
 As a result, it can be rephrased in the language of probability, e.g. using a sequence of random variables and [expected values](https://en.wikipedia.org/wiki/Expected_value "Expected value")
. The theorem is named after [John Kingman](https://en.wikipedia.org/wiki/John_Kingman "John Kingman")
.

Contents
--------

*   [1 Statement of theorem](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#Statement_of_theorem)
    *   [1.1 Equivalent statement](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#Equivalent_statement)
        
*   [2 Proof](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#Proof)
    *   [2.1 Subadditivity by partition](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#Subadditivity_by_partition)
        
    *   [2.2 Constructing _g_](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#Constructing_g)
        
    *   [2.3 Reducing to the case of _gn ≤ 0_](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#Reducing_to_the_case_of_gn_%E2%89%A4_0)
        
    *   [2.4 Bounding the truncation](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#Bounding_the_truncation)
        
    *   [2.5 Peeling off the first qualifier](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#Peeling_off_the_first_qualifier)
        
    *   [2.6 Peeling off the second qualifier](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#Peeling_off_the_second_qualifier)
        
*   [3 Applications](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#Applications)
    *   [3.1 Longest increasing subsequence](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#Longest_increasing_subsequence)
        
*   [4 References](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#References)
    

Statement of theorem
--------------------

[edit](https://en.wikipedia.org/w/index.php?title=Kingman%27s_subadditive_ergodic_theorem&action=edit&section=1 "Edit section: Statement of theorem")

Let T {\\displaystyle T} ![{\displaystyle T}](https://wikimedia.org/api/rest_v1/media/math/render/svg/ec7200acd984a1d3a3d7dc455e262fbe54f7f6e0) be a [measure-preserving transformation](https://en.wikipedia.org/wiki/Measure-preserving_dynamical_system "Measure-preserving dynamical system")
 on the [probability space](https://en.wikipedia.org/wiki/Probability_space "Probability space")
 ( Ω , Σ , μ ) {\\displaystyle (\\Omega ,\\Sigma ,\\mu )} ![{\displaystyle (\Omega ,\Sigma ,\mu )}](https://wikimedia.org/api/rest_v1/media/math/render/svg/22ed3b570455214147b8afded02ac578a0ba86e3) , and let { g n } n ∈ N {\\displaystyle \\{g\_{n}\\}\_{n\\in \\mathbb {N} }} ![{\displaystyle \{g_{n}\}_{n\in \mathbb {N} }}](https://wikimedia.org/api/rest_v1/media/math/render/svg/d96a11b2e6ee01129b5101e7f27c1b686f83af57) be a sequence of L 1 {\\displaystyle L^{1}} ![{\displaystyle L^{1}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/74c288d1089f1ec85b01b4de25c441fc792bd2d9) functions such that g n + m ( x ) ≤ g n ( x ) + g m ( T n x ) {\\displaystyle g\_{n+m}(x)\\leq g\_{n}(x)+g\_{m}(T^{n}x)} ![{\displaystyle g_{n+m}(x)\leq g_{n}(x)+g_{m}(T^{n}x)}](https://wikimedia.org/api/rest_v1/media/math/render/svg/2434f0e066e21284ca021371ba4d0745c598485a) (subadditivity relation). Then

lim n → ∞ g n ( x ) n \=: g ( x ) ≥ − ∞ {\\displaystyle \\lim \_{n\\to \\infty }{\\frac {g\_{n}(x)}{n}}=:g(x)\\geq -\\infty } ![{\displaystyle \lim _{n\to \infty }{\frac {g_{n}(x)}{n}}=:g(x)\geq -\infty }](https://wikimedia.org/api/rest_v1/media/math/render/svg/0cf38cbc70d113cc053c3529916ed4fb5835a1d5) 

for μ {\\displaystyle \\mu } ![{\displaystyle \mu }](https://wikimedia.org/api/rest_v1/media/math/render/svg/9fd47b2a39f7a7856952afec1f1db72c67af6161) \-a.e. _x_, where _g_(_x_) is _T_\-invariant.

In particular, if _T_ is [ergodic](https://en.wikipedia.org/wiki/Ergodicity "Ergodicity")
, then _g_(_x_) is a constant.

### Equivalent statement

[edit](https://en.wikipedia.org/w/index.php?title=Kingman%27s_subadditive_ergodic_theorem&action=edit&section=2 "Edit section: Equivalent statement")

Given a family of real random variables X ( m , n ) {\\textstyle X(m,n)} ![{\textstyle X(m,n)}](https://wikimedia.org/api/rest_v1/media/math/render/svg/8f04cdbcc56b9be8bd87c28f8f1c16db62f9eb38) , with 0 ≤ m < n ∈ N {\\textstyle 0\\leq m<n\\in \\mathbb {N} } ![{\textstyle 0\leq m<n\in \mathbb {N} }](https://wikimedia.org/api/rest_v1/media/math/render/svg/b76bd139fca12ea202fc00861bbf912f9df0f1d7) , such that they are subadditive in the sense that X ( m + 1 , n + 1 ) \= X ( m , n ) ∘ T X ( 0 , n ) ≤ X ( 0 , m ) + X ( m , n ) {\\displaystyle {\\begin{aligned}&X(m+1,n+1)=X(m,n)\\circ T\\\\&X(0,n)\\leq X(0,m)+X(m,n)\\end{aligned}}} ![{\displaystyle {\begin{aligned}&X(m+1,n+1)=X(m,n)\circ T\\&X(0,n)\leq X(0,m)+X(m,n)\end{aligned}}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/8e4d3a1736eb75a25042cf0aac2666dbb3cf7089) Then there exists a random variable Y {\\textstyle Y} ![{\textstyle Y}](https://wikimedia.org/api/rest_v1/media/math/render/svg/6222becc4f0c5effa012e5335b170575fdbbaad3) such that Y ∈ \[ − ∞ , + ∞ ) {\\textstyle Y\\in \[-\\infty ,+\\infty )} ![{\textstyle Y\in [-\infty ,+\infty )}](https://wikimedia.org/api/rest_v1/media/math/render/svg/012485328867819fefe9314f8e67af85d5ef6924) , Y {\\textstyle Y} ![{\textstyle Y}](https://wikimedia.org/api/rest_v1/media/math/render/svg/6222becc4f0c5effa012e5335b170575fdbbaad3) is invariant with respect to T {\\textstyle T} ![{\textstyle T}](https://wikimedia.org/api/rest_v1/media/math/render/svg/db299e88e5485f250f4ba15530469c8c6080a8cb) , and lim n 1 n X ( 0 , n ) \= Y {\\textstyle \\lim \_{n}{\\frac {1}{n}}X(0,n)=Y} ![{\textstyle \lim _{n}{\frac {1}{n}}X(0,n)=Y}](https://wikimedia.org/api/rest_v1/media/math/render/svg/6443d03b432322d1618fc7fee60d97b101f3b1bc) a.s..\
\
They are equivalent by setting\
\
*   g n \= X ( 0 , n ) {\\textstyle g\_{n}=X(0,n)} ![{\textstyle g_{n}=X(0,n)}](https://wikimedia.org/api/rest_v1/media/math/render/svg/345eb0076052985d6ea8b61d73c40903d378a3a4) with n ≥ 1 {\\textstyle n\\geq 1} ![{\textstyle n\geq 1}](https://wikimedia.org/api/rest_v1/media/math/render/svg/f7656f5c4d7484d20db41c9536df9560dfd84593) ;\
*   X ( m , m + n ) \= g n ∘ T m {\\textstyle X(m,m+n)=g\_{n}\\circ T^{m}} ![{\textstyle X(m,m+n)=g_{n}\circ T^{m}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/6d6f8f7d0c7136cd549abf0e3bfcca549337995a) with m ≥ 0 {\\textstyle m\\geq 0} ![{\textstyle m\geq 0}](https://wikimedia.org/api/rest_v1/media/math/render/svg/2e741d2816f96c7b4099668606a58fd71bc7af93) .\
\
Proof\
-----\
\
[edit](https://en.wikipedia.org/w/index.php?title=Kingman%27s_subadditive_ergodic_theorem&action=edit&section=3 "Edit section: Proof")\
\
Proof due to ([J. Michael Steele](https://en.wikipedia.org/wiki/J._Michael_Steele "J. Michael Steele")\
, 1989).[\[3\]](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#cite_note-3)\
\
### Subadditivity by partition\
\
[edit](https://en.wikipedia.org/w/index.php?title=Kingman%27s_subadditive_ergodic_theorem&action=edit&section=4 "Edit section: Subadditivity by partition")\
\
Fix some n ≥ 1 {\\textstyle n\\geq 1} ![{\textstyle n\geq 1}](https://wikimedia.org/api/rest_v1/media/math/render/svg/f7656f5c4d7484d20db41c9536df9560dfd84593) . By subadditivity, for any l ∈ 1 : n − 1 {\\textstyle l\\in 1:n-1} ![{\textstyle l\in 1:n-1}](https://wikimedia.org/api/rest_v1/media/math/render/svg/620ead83c846c88e907804265cc8be8529afb0fb) g n ≤ g n − l + g l ∘ T n − l {\\displaystyle g\_{n}\\leq g\_{n-l}+g\_{l}\\circ T^{n-l}} ![{\displaystyle g_{n}\leq g_{n-l}+g_{l}\circ T^{n-l}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/53f80194e220848c8ffa93a412773435990f0dca) \
\
We can picture this as starting with the set 0 : n − 1 {\\textstyle 0:n-1} ![{\textstyle 0:n-1}](https://wikimedia.org/api/rest_v1/media/math/render/svg/69559ee33d8e6982178786aa94273ecdd2680459) , and then removing its length l {\\textstyle l} ![{\textstyle l}](https://wikimedia.org/api/rest_v1/media/math/render/svg/a272396a098706dc62adc4bb977a8cc79739021f) tail.\
\
Repeating this construction until the set 0 : n − 1 {\\textstyle 0:n-1} ![{\textstyle 0:n-1}](https://wikimedia.org/api/rest_v1/media/math/render/svg/69559ee33d8e6982178786aa94273ecdd2680459) is all gone, we have a one-to-one correspondence between upper bounds of g n {\\textstyle g\_{n}} ![{\textstyle g_{n}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/5cffe320ba81a69bdabb6d45201f848f92d83b2e) and partitions of 1 : n − 1 {\\textstyle 1:n-1} ![{\textstyle 1:n-1}](https://wikimedia.org/api/rest_v1/media/math/render/svg/c36b419596f5176dab62cbdb780347c45ee7d60c) .\
\
Specifically, let { k i : ( k i + l i − 1 ) } i {\\textstyle \\{k\_{i}:(k\_{i}+l\_{i}-1)\\}\_{i}} ![{\textstyle \{k_{i}:(k_{i}+l_{i}-1)\}_{i}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/cbdecaf75bebbb44a3d37c5948f2de16592e03c3) be a partition of 0 : n − 1 {\\textstyle 0:n-1} ![{\textstyle 0:n-1}](https://wikimedia.org/api/rest_v1/media/math/render/svg/69559ee33d8e6982178786aa94273ecdd2680459) , then we have g n ≤ ∑ i g l i ∘ T k i {\\displaystyle g\_{n}\\leq \\sum \_{i}g\_{l\_{i}}\\circ T^{k\_{i}}} ![{\displaystyle g_{n}\leq \sum _{i}g_{l_{i}}\circ T^{k_{i}}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/12e8c81428d5bba328abc4fd4fe1daaf8f16c575) \
\
### Constructing _g_\
\
[edit](https://en.wikipedia.org/w/index.php?title=Kingman%27s_subadditive_ergodic_theorem&action=edit&section=5 "Edit section: Constructing g")\
\
Let g := lim inf g n / n {\\textstyle g:=\\liminf g\_{n}/n} ![{\textstyle g:=\liminf g_{n}/n}](https://wikimedia.org/api/rest_v1/media/math/render/svg/8e5657b767b94234c3e21b3d35e3bf81ad196376) , then it is T {\\textstyle T} ![{\textstyle T}](https://wikimedia.org/api/rest_v1/media/math/render/svg/db299e88e5485f250f4ba15530469c8c6080a8cb) \-invariant.\
\
By subadditivity, g n + 1 n + 1 ≤ g 1 + g n ∘ T n + 1 {\\displaystyle {\\frac {g\_{n+1}}{n+1}}\\leq {\\frac {g\_{1}+g\_{n}\\circ T}{n+1}}} ![{\displaystyle {\frac {g_{n+1}}{n+1}}\leq {\frac {g_{1}+g_{n}\circ T}{n+1}}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/80cdea0d84c023560cf9f6e0b7e135ad9d52235e) \
\
Taking the n → ∞ {\\textstyle n\\to \\infty } ![{\textstyle n\to \infty }](https://wikimedia.org/api/rest_v1/media/math/render/svg/b2e2d57fbe15926e75495e28e3517ffec3622d96) limit, we have g ≤ g ∘ T {\\displaystyle g\\leq g\\circ T} ![{\displaystyle g\leq g\circ T}](https://wikimedia.org/api/rest_v1/media/math/render/svg/79e8854ec310601743af2e9d446d3de705f1ca77) We can visualize T {\\textstyle T} ![{\textstyle T}](https://wikimedia.org/api/rest_v1/media/math/render/svg/db299e88e5485f250f4ba15530469c8c6080a8cb) as hill-climbing on the graph of g {\\textstyle g} ![{\textstyle g}](https://wikimedia.org/api/rest_v1/media/math/render/svg/38dc9ad184fe5486391b456b9e68767ff77f3719) . If T {\\textstyle T} ![{\textstyle T}](https://wikimedia.org/api/rest_v1/media/math/render/svg/db299e88e5485f250f4ba15530469c8c6080a8cb) actually causes a nontrivial amount of hill-climbing, then we would get a spatial contraction, and so T {\\textstyle T} ![{\textstyle T}](https://wikimedia.org/api/rest_v1/media/math/render/svg/db299e88e5485f250f4ba15530469c8c6080a8cb) does not preserve measure. Therefore g \= g ∘ T {\\textstyle g=g\\circ T} ![{\textstyle g=g\circ T}](https://wikimedia.org/api/rest_v1/media/math/render/svg/dbb4a38c61d10bc4382c622af85b3637650aebf9) a.e.\
\
Let c ∈ R {\\textstyle c\\in \\mathbb {R} } ![{\textstyle c\in \mathbb {R} }](https://wikimedia.org/api/rest_v1/media/math/render/svg/e9b91e9e88acfa9220a1e7fc11dc11b44f835c84) , then { g ≥ c } ⊂ { g ∘ T ≥ c } \= T − 1 ( { g ≥ c } ) {\\displaystyle \\{g\\geq c\\}\\subset \\{g\\circ T\\geq c\\}=T^{-1}(\\{g\\geq c\\})} ![{\displaystyle \{g\geq c\}\subset \{g\circ T\geq c\}=T^{-1}(\{g\geq c\})}](https://wikimedia.org/api/rest_v1/media/math/render/svg/82ec6b4652ed66aed070a4400927cdb924a6a19e) and since both sides have the same measure, by squeezing, they are equal a.e..\
\
That is, g ( x ) ≥ c ⟺ g ( T x ) ≥ c {\\textstyle g(x)\\geq c\\iff g(Tx)\\geq c} ![{\textstyle g(x)\geq c\iff g(Tx)\geq c}](https://wikimedia.org/api/rest_v1/media/math/render/svg/390a45fc779f6196c29dfac62694f6240c42a00a) , a.e..\
\
Now apply this for all rational c {\\textstyle c} ![{\textstyle c}](https://wikimedia.org/api/rest_v1/media/math/render/svg/7d411ca19645ddd4fff0704de95ec770681093bb) .\
\
### Reducing to the case of _gn ≤ 0_\
\
[edit](https://en.wikipedia.org/w/index.php?title=Kingman%27s_subadditive_ergodic_theorem&action=edit&section=6 "Edit section: Reducing to the case of gn ≤ 0")\
\
  \
By subadditivity, using the partition of 0 : n − 1 {\\textstyle 0:n-1} ![{\textstyle 0:n-1}](https://wikimedia.org/api/rest_v1/media/math/render/svg/69559ee33d8e6982178786aa94273ecdd2680459) into singletons. g 1 ≤ g 1 g 2 ≤ g 1 + g 1 ∘ T g 3 ≤ g 1 + g 1 ∘ T + g 1 ∘ T 2 ⋯ {\\displaystyle {\\begin{aligned}g\_{1}&\\leq g\_{1}\\\\g\_{2}&\\leq g\_{1}+g\_{1}\\circ T\\\\g\_{3}&\\leq g\_{1}+g\_{1}\\circ T+g\_{1}\\circ T^{2}\\\\&\\cdots \\end{aligned}}} ![{\displaystyle {\begin{aligned}g_{1}&\leq g_{1}\\g_{2}&\leq g_{1}+g_{1}\circ T\\g_{3}&\leq g_{1}+g_{1}\circ T+g_{1}\circ T^{2}\\&\cdots \end{aligned}}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/56aebc3ea9423d251f1991741edad3a0dd6206b5) Now, construct the sequence f 1 \= g 1 − g 1 f 2 \= g 2 − ( g 1 + g 1 ∘ T ) f 3 \= g 3 − ( g 1 + g 1 ∘ T + g 1 ∘ T 2 ) ⋯ {\\displaystyle {\\begin{aligned}f\_{1}&=g\_{1}-g\_{1}\\\\f\_{2}&=g\_{2}-(g\_{1}+g\_{1}\\circ T)\\\\f\_{3}&=g\_{3}-(g\_{1}+g\_{1}\\circ T+g\_{1}\\circ T^{2})\\\\&\\cdots \\end{aligned}}} ![{\displaystyle {\begin{aligned}f_{1}&=g_{1}-g_{1}\\f_{2}&=g_{2}-(g_{1}+g_{1}\circ T)\\f_{3}&=g_{3}-(g_{1}+g_{1}\circ T+g_{1}\circ T^{2})\\&\cdots \end{aligned}}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/1fd13598f264738939bc13c46d041d83840979bc) which satisfies f n ≤ 0 {\\textstyle f\_{n}\\leq 0} ![{\textstyle f_{n}\leq 0}](https://wikimedia.org/api/rest_v1/media/math/render/svg/313678076fedc533a4de014205947393e0f2b63c) for all n {\\textstyle n} ![{\textstyle n}](https://wikimedia.org/api/rest_v1/media/math/render/svg/cc6e1f880981346a604257ebcacdef24c0aca2d6) .\
\
By the special case, f n / n {\\textstyle f\_{n}/n} ![{\textstyle f_{n}/n}](https://wikimedia.org/api/rest_v1/media/math/render/svg/bc43e0a63670ae0915548b061940cb5e64556678) converges a.e. to a T {\\textstyle T} ![{\textstyle T}](https://wikimedia.org/api/rest_v1/media/math/render/svg/db299e88e5485f250f4ba15530469c8c6080a8cb) \-invariant function.\
\
By Birkhoff's pointwise ergodic theorem, the running average 1 n ( g 1 + g 1 ∘ T + g 1 ∘ T 2 + ⋯ ) {\\displaystyle {\\frac {1}{n}}(g\_{1}+g\_{1}\\circ T+g\_{1}\\circ T^{2}+\\cdots )} ![{\displaystyle {\frac {1}{n}}(g_{1}+g_{1}\circ T+g_{1}\circ T^{2}+\cdots )}](https://wikimedia.org/api/rest_v1/media/math/render/svg/c85f13a8080fae7c4366b0e984e36eda17278ce5) converges a.e. to a T {\\textstyle T} ![{\textstyle T}](https://wikimedia.org/api/rest_v1/media/math/render/svg/db299e88e5485f250f4ba15530469c8c6080a8cb) \-invariant function. Therefore, their sum does as well.\
\
### Bounding the truncation\
\
[edit](https://en.wikipedia.org/w/index.php?title=Kingman%27s_subadditive_ergodic_theorem&action=edit&section=7 "Edit section: Bounding the truncation")\
\
Fix arbitrary ϵ , M \> 0 {\\textstyle \\epsilon ,M>0} ![{\textstyle \epsilon ,M>0}](https://wikimedia.org/api/rest_v1/media/math/render/svg/54d6fa66b12948643e22b68fe7a7e91e2fd9e6e8) , and construct the truncated function, still T {\\textstyle T} ![{\textstyle T}](https://wikimedia.org/api/rest_v1/media/math/render/svg/db299e88e5485f250f4ba15530469c8c6080a8cb) \-invariant: g ′ := max ( g , − M ) {\\displaystyle g':=\\max(g,-M)} ![{\displaystyle g':=\max(g,-M)}](https://wikimedia.org/api/rest_v1/media/math/render/svg/ed54fa1c2e65dbfdc29ba2bb081683770bc2e1f0) With these, it suffices to prove an a.e. upper bound lim sup g n / n ≤ g ′ + ϵ {\\displaystyle \\limsup g\_{n}/n\\leq g'+\\epsilon } ![{\displaystyle \limsup g_{n}/n\leq g'+\epsilon }](https://wikimedia.org/api/rest_v1/media/math/render/svg/efe7e6d7175e766c5f9250e180b5befd67e70a3d) since it would allow us to take the limit ϵ \= 1 / 1 , 1 / 2 , 1 / 3 , … {\\textstyle \\epsilon =1/1,1/2,1/3,\\dots } ![{\textstyle \epsilon =1/1,1/2,1/3,\dots }](https://wikimedia.org/api/rest_v1/media/math/render/svg/bce845e95bc75f4811b582fae571835dc6307ea9) , then the limit M \= 1 , 2 , 3 , … {\\textstyle M=1,2,3,\\dots } ![{\textstyle M=1,2,3,\dots }](https://wikimedia.org/api/rest_v1/media/math/render/svg/396dd3a33a584472442fdc3ef5aa36eadbcd7e4d) , giving us a.e.\
\
lim sup g n / n ≤ lim inf g n / n \=: g {\\displaystyle \\limsup g\_{n}/n\\leq \\liminf g\_{n}/n=:g} ![{\displaystyle \limsup g_{n}/n\leq \liminf g_{n}/n=:g}](https://wikimedia.org/api/rest_v1/media/math/render/svg/20a299a3649740a500a1a9ebcdabf2509653be7d) And by squeezing, we have g n / n {\\textstyle g\_{n}/n} ![{\textstyle g_{n}/n}](https://wikimedia.org/api/rest_v1/media/math/render/svg/394026cd0bb372f72768a943ea3bc6a6371c0359) converging a.e. to g {\\textstyle g} ![{\textstyle g}](https://wikimedia.org/api/rest_v1/media/math/render/svg/38dc9ad184fe5486391b456b9e68767ff77f3719) . Define two families of sets, one shrinking to the [empty set](https://en.wikipedia.org/wiki/Empty_set "Empty set")\
, and one growing to the full set. For each "length" L \= 1 , 2 , 3 , … {\\displaystyle L=1,2,3,\\dots } ![{\displaystyle L=1,2,3,\dots }](https://wikimedia.org/api/rest_v1/media/math/render/svg/873c314e5e8d8becdc0ca003423cd023d3aa0595) , define B L := { x : g l / l \> g ′ + ϵ , ∀ l ∈ 1 , 2 , … , L } {\\displaystyle B\_{L}:=\\{x:g\_{l}/l>g'+\\epsilon ,\\forall l\\in 1,2,\\dots ,L\\}} ![{\displaystyle B_{L}:=\{x:g_{l}/l>g'+\epsilon ,\forall l\in 1,2,\dots ,L\}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/d36fcc132405c3626dd1a570550d771f6a799811) A L := B L c \= { x : g l / l ≤ g ′ + ϵ , ∃ l ∈ 1 , 2 , … , L } {\\displaystyle A\_{L}:=B\_{L}^{c}=\\{x:g\_{l}/l\\leq g'+\\epsilon ,\\exists l\\in 1,2,\\dots ,L\\}} ![{\displaystyle A_{L}:=B_{L}^{c}=\{x:g_{l}/l\leq g'+\epsilon ,\exists l\in 1,2,\dots ,L\}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/aabca7bd66ae96d8623606bcb71dd9d280d8e766) Since g ′ ≥ lim inf g n / n {\\textstyle g'\\geq \\liminf g\_{n}/n} ![{\textstyle g'\geq \liminf g_{n}/n}](https://wikimedia.org/api/rest_v1/media/math/render/svg/2fa10dff70783da60d241d486b47218620668857) , the B {\\textstyle B} ![{\textstyle B}](https://wikimedia.org/api/rest_v1/media/math/render/svg/de0b47ffc21636dc2df68f6c793177a268f10e9b) family shrinks to the empty set.\
\
  \
Fix x ∈ X {\\textstyle x\\in X} ![{\textstyle x\in X}](https://wikimedia.org/api/rest_v1/media/math/render/svg/21d7c0406757a1b48249ee3d5577e8d93fbaaa1d) . Fix L ∈ N {\\textstyle L\\in \\mathbb {N} } ![{\textstyle L\in \mathbb {N} }](https://wikimedia.org/api/rest_v1/media/math/render/svg/9e43756509ed1dd6f81649ac027a305eb7c6518a) . Fix n \> L {\\textstyle n>L} ![{\textstyle n>L}](https://wikimedia.org/api/rest_v1/media/math/render/svg/aa391fcca598895f64bf296eaf58214a4490bf81) . The ordering of these qualifiers is vitally important, because we will be removing the qualifiers one by one in the reverse order.\
\
To prove the a.e. upper bound, we must use the subadditivity, which means we must construct a partition of the set 0 : n − 1 {\\textstyle 0:n-1} ![{\textstyle 0:n-1}](https://wikimedia.org/api/rest_v1/media/math/render/svg/69559ee33d8e6982178786aa94273ecdd2680459) . We do this inductively:\
\
> Take the smallest k {\\textstyle k} ![{\textstyle k}](https://wikimedia.org/api/rest_v1/media/math/render/svg/0d5595fc0c47452f8fc2aa6e29c3611f047714b0) not already in a partition.\
\
> If T k x ∈ A N {\\textstyle T^{k}x\\in A\_{N}} ![{\textstyle T^{k}x\in A_{N}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/98ff3914adbf54286b0c130a15744ef9b26aa96a) , then g l ( T k x ) / l ≤ g ′ ( x ) + ϵ {\\textstyle g\_{l}(T^{k}x)/l\\leq g'(x)+\\epsilon } ![{\textstyle g_{l}(T^{k}x)/l\leq g'(x)+\epsilon }](https://wikimedia.org/api/rest_v1/media/math/render/svg/52550485884e72ab7c055edb25bf6718b64141f1) for some l ∈ 1 , 2 , … L {\\textstyle l\\in 1,2,\\dots L} ![{\textstyle l\in 1,2,\dots L}](https://wikimedia.org/api/rest_v1/media/math/render/svg/eb71c5dfeb977ddeabec68e955fff3a40f2768d0) . Take one such l {\\textstyle l} ![{\textstyle l}](https://wikimedia.org/api/rest_v1/media/math/render/svg/a272396a098706dc62adc4bb977a8cc79739021f) – the choice does not matter.\
\
> If k + l − 1 ≤ n − 1 {\\textstyle k+l-1\\leq n-1} ![{\textstyle k+l-1\leq n-1}](https://wikimedia.org/api/rest_v1/media/math/render/svg/bf5f92223165fae4534c462135c8b86ff6acd677) , then we cut out { k , … , k + l − 1 } {\\textstyle \\{k,\\dots ,k+l-1\\}} ![{\textstyle \{k,\dots ,k+l-1\}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/e4eb57a25892aac00f7b7e2658d5ebdb9c0acdc2) . Call these partitions "type 1". Else, we cut out { k } {\\textstyle \\{k\\}} ![{\textstyle \{k\}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/a70f4ade9710a9606e9d1d6c3cd7f67863218178) . Call these partitions "type 2".\
\
> Else, we cut out { k } {\\textstyle \\{k\\}} ![{\textstyle \{k\}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/a70f4ade9710a9606e9d1d6c3cd7f67863218178) . Call these partitions "type 3".\
\
Now convert this partition into an inequality: g n ( x ) ≤ ∑ i g l i ( T k i x ) {\\displaystyle g\_{n}(x)\\leq \\sum \_{i}g\_{l\_{i}}(T^{k\_{i}}x)} ![{\displaystyle g_{n}(x)\leq \sum _{i}g_{l_{i}}(T^{k_{i}}x)}](https://wikimedia.org/api/rest_v1/media/math/render/svg/2696fa427d1a723e3724e58e11b6cfd7a415a862) where k i {\\textstyle k\_{i}} ![{\textstyle k_{i}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/13d91731bf4e9bceddd8afde03a9a191f6d36dfa) are the heads of the partitions, and l i {\\textstyle l\_{i}} ![{\textstyle l_{i}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/6ef442e144bf72378ef6b726a6e9e52e45fe55d3) are the lengths.\
\
Since all g n ≤ 0 {\\textstyle g\_{n}\\leq 0} ![{\textstyle g_{n}\leq 0}](https://wikimedia.org/api/rest_v1/media/math/render/svg/9de29111b10ce05838efedabecce1873138fdd33) , we can remove the other kinds of partitions: g n ( x ) ≤ ∑ i : type 1 g l i ( T k i x ) {\\displaystyle g\_{n}(x)\\leq \\sum \_{i:{\\text{type 1}}}g\_{l\_{i}}(T^{k\_{i}}x)} ![{\displaystyle g_{n}(x)\leq \sum _{i:{\text{type 1}}}g_{l_{i}}(T^{k_{i}}x)}](https://wikimedia.org/api/rest_v1/media/math/render/svg/e085bff1a33ec077616082b596912ce069a72ac1) By construction, each g l i ( T k i x ) ≤ l i ( g ′ ( x ) + ϵ ) {\\textstyle g\_{l\_{i}}(T^{k\_{i}}x)\\leq l\_{i}(g'(x)+\\epsilon )} ![{\textstyle g_{l_{i}}(T^{k_{i}}x)\leq l_{i}(g'(x)+\epsilon )}](https://wikimedia.org/api/rest_v1/media/math/render/svg/ccf10358ee2f6e21d14184d48a6db953668cf882) , thus 1 n g n ( x ) ≤ g ′ ( x ) 1 n ∑ i : type 1 l i + ϵ {\\displaystyle {\\frac {1}{n}}g\_{n}(x)\\leq g'(x){\\frac {1}{n}}\\sum \_{i:{\\text{type 1}}}l\_{i}+\\epsilon } ![{\displaystyle {\frac {1}{n}}g_{n}(x)\leq g'(x){\frac {1}{n}}\sum _{i:{\text{type 1}}}l_{i}+\epsilon }](https://wikimedia.org/api/rest_v1/media/math/render/svg/9d72af04ccc64e8b7b88ad136aba6cdf62cca7b4) Now it would be tempting to continue with g ′ ( x ) 1 n ∑ i : type 1 l i ≤ g ′ ( x ) {\\textstyle g'(x){\\frac {1}{n}}\\sum \_{i:{\\text{type 1}}}l\_{i}\\leq g'(x)} ![{\textstyle g'(x){\frac {1}{n}}\sum _{i:{\text{type 1}}}l_{i}\leq g'(x)}](https://wikimedia.org/api/rest_v1/media/math/render/svg/6c86b34406dc54343fa310db81bbf4af459a595a) , but unfortunately g ′ ≤ 0 {\\textstyle g'\\leq 0} ![{\textstyle g'\leq 0}](https://wikimedia.org/api/rest_v1/media/math/render/svg/de14e75c2dd1593881e505744a3823ceae6cac00) , so the direction is the exact opposite. We must _lower_ bound the sum ∑ i : type 1 l i {\\textstyle \\sum \_{i:{\\text{type 1}}}l\_{i}} ![{\textstyle \sum _{i:{\text{type 1}}}l_{i}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/3b74bf1ec9c6baf0cec08eff26101862e879ba1d) .\
\
The number of type 3 elements is equal to ∑ k ∈ 0 : n − 1 1 B L ( T k x ) {\\displaystyle \\sum \_{k\\in 0:n-1}1\_{B\_{L}}(T^{k}x)} ![{\displaystyle \sum _{k\in 0:n-1}1_{B_{L}}(T^{k}x)}](https://wikimedia.org/api/rest_v1/media/math/render/svg/aa44d8087fb3e757769667baacc6db79884780fe) If a number k {\\textstyle k} ![{\textstyle k}](https://wikimedia.org/api/rest_v1/media/math/render/svg/0d5595fc0c47452f8fc2aa6e29c3611f047714b0) is of type 2, then it must be inside the last L − 1 {\\textstyle L-1} ![{\textstyle L-1}](https://wikimedia.org/api/rest_v1/media/math/render/svg/0f7295ef18de5c18f18635342dc9ba3b10d3bd51) elements of 0 : n − 1 {\\textstyle 0:n-1} ![{\textstyle 0:n-1}](https://wikimedia.org/api/rest_v1/media/math/render/svg/69559ee33d8e6982178786aa94273ecdd2680459) . Thus the number of type 2 elements is at most L − 1 {\\textstyle L-1} ![{\textstyle L-1}](https://wikimedia.org/api/rest_v1/media/math/render/svg/0f7295ef18de5c18f18635342dc9ba3b10d3bd51) . Together, we have the _lower_ bound: 1 n ∑ i : type 1 l i ≥ 1 − L − 1 n − 1 n ∑ k ∈ 0 : n − 1 1 B L ( T k x ) {\\displaystyle {\\frac {1}{n}}\\sum \_{i:{\\text{type 1}}}l\_{i}\\geq 1-{\\frac {L-1}{n}}-{\\frac {1}{n}}\\sum \_{k\\in 0:n-1}1\_{B\_{L}}(T^{k}x)} ![{\displaystyle {\frac {1}{n}}\sum _{i:{\text{type 1}}}l_{i}\geq 1-{\frac {L-1}{n}}-{\frac {1}{n}}\sum _{k\in 0:n-1}1_{B_{L}}(T^{k}x)}](https://wikimedia.org/api/rest_v1/media/math/render/svg/e529c2480620a94bbaef40824cb8f259a1676694) \
\
### Peeling off the first qualifier\
\
[edit](https://en.wikipedia.org/w/index.php?title=Kingman%27s_subadditive_ergodic_theorem&action=edit&section=8 "Edit section: Peeling off the first qualifier")\
\
Remove the n \> L {\\textstyle n>L} ![{\textstyle n>L}](https://wikimedia.org/api/rest_v1/media/math/render/svg/aa391fcca598895f64bf296eaf58214a4490bf81) qualifier by taking the n → ∞ {\\textstyle n\\to \\infty } ![{\textstyle n\to \infty }](https://wikimedia.org/api/rest_v1/media/math/render/svg/b2e2d57fbe15926e75495e28e3517ffec3622d96) limit.\
\
By Birkhoff's pointwise ergodic theorem, there exists an a.e. pointwise limit lim n 1 n ∑ k ∈ 0 : n − 1 1 B L ( T k x ) → 1 ¯ B L ( x ) {\\displaystyle \\lim \_{n}{\\frac {1}{n}}\\sum \_{k\\in 0:n-1}1\_{B\_{L}}(T^{k}x)\\to {\\bar {1}}\_{B\_{L}}(x)} ![{\displaystyle \lim _{n}{\frac {1}{n}}\sum _{k\in 0:n-1}1_{B_{L}}(T^{k}x)\to {\bar {1}}_{B_{L}}(x)}](https://wikimedia.org/api/rest_v1/media/math/render/svg/d7d3e4ee69dea9a2d88667a446a1642b9d5d6eb9) satisfying  \
∫ 1 ¯ B L \= μ ( B L ) ; 1 ¯ B L ( x ) ∈ \[ 0 , 1 \] {\\displaystyle \\int {\\bar {1}}\_{B\_{L}}=\\mu (B\_{L});\\quad {\\bar {1}}\_{B\_{L}}(x)\\in \[0,1\]} ![{\displaystyle \int {\bar {1}}_{B_{L}}=\mu (B_{L});\quad {\bar {1}}_{B_{L}}(x)\in [0,1]}](https://wikimedia.org/api/rest_v1/media/math/render/svg/dece87dd63ea759ccc4eacde0cd390c30988f9f0) At the limit, we find that for a.e. x ∈ X , L ∈ N {\\textstyle x\\in X,L\\in \\mathbb {N} } ![{\textstyle x\in X,L\in \mathbb {N} }](https://wikimedia.org/api/rest_v1/media/math/render/svg/3ff61d1223f456a1062adf57aecb458c66632557) , lim sup n g n ( x ) n ≤ g ′ ( x ) ( 1 − 1 ¯ B L ( x ) ) + ϵ {\\displaystyle \\limsup \_{n}{\\frac {g\_{n}(x)}{n}}\\leq g'(x)(1-{\\bar {1}}\_{B\_{L}}(x))+\\epsilon } ![{\displaystyle \limsup _{n}{\frac {g_{n}(x)}{n}}\leq g'(x)(1-{\bar {1}}_{B_{L}}(x))+\epsilon }](https://wikimedia.org/api/rest_v1/media/math/render/svg/f3afa297f621e0b1891caf2c5cd607b3158af031) \
\
### Peeling off the second qualifier\
\
[edit](https://en.wikipedia.org/w/index.php?title=Kingman%27s_subadditive_ergodic_theorem&action=edit&section=9 "Edit section: Peeling off the second qualifier")\
\
Remove the L ∈ N {\\textstyle L\\in \\mathbb {N} } ![{\textstyle L\in \mathbb {N} }](https://wikimedia.org/api/rest_v1/media/math/render/svg/9e43756509ed1dd6f81649ac027a305eb7c6518a) qualifier by taking the L → ∞ {\\textstyle L\\to \\infty } ![{\textstyle L\to \infty }](https://wikimedia.org/api/rest_v1/media/math/render/svg/89009df08871b86485d1f7e3d0dcdc053966dbac) limit.\
\
Since we have ∫ 1 ¯ B L \= μ ( B L ) → 0 {\\displaystyle \\int {\\bar {1}}\_{B\_{L}}=\\mu (B\_{L})\\to 0} ![{\displaystyle \int {\bar {1}}_{B_{L}}=\mu (B_{L})\to 0}](https://wikimedia.org/api/rest_v1/media/math/render/svg/0ef3af74af00734b68677c2349959f83b04069ef) and 1 ¯ B L ≥ 1 ¯ B L + 1 ≥ ⋯ {\\displaystyle {\\bar {1}}\_{B\_{L}}\\geq {\\bar {1}}\_{B\_{L+1}}\\geq \\cdots } ![{\displaystyle {\bar {1}}_{B_{L}}\geq {\bar {1}}_{B_{L+1}}\geq \cdots }](https://wikimedia.org/api/rest_v1/media/math/render/svg/ea94897a0ef66d0a781f4e4a3950e9ab4cceecbe) as 1 B L ≥ 1 B L + 1 ≥ ⋯ {\\displaystyle 1\_{B\_{L}}\\geq 1\_{B\_{L+1}}\\geq \\cdots } ![{\displaystyle 1_{B_{L}}\geq 1_{B_{L+1}}\geq \cdots }](https://wikimedia.org/api/rest_v1/media/math/render/svg/73164a29d5a27e683e87919c3e1437a8bff901ab) , we can apply the same argument used for proving [Markov's inequality](https://en.wikipedia.org/wiki/Markov's_inequality "Markov's inequality")\
, to obtain  \
lim sup n g n ( x ) n ≤ g ′ ( x ) + ϵ {\\displaystyle \\limsup \_{n}{\\frac {g\_{n}(x)}{n}}\\leq g'(x)+\\epsilon } ![{\displaystyle \limsup _{n}{\frac {g_{n}(x)}{n}}\leq g'(x)+\epsilon }](https://wikimedia.org/api/rest_v1/media/math/render/svg/87ee161c80d8fe0bb2c7ec4748f7a6baf1f6368f) for a.e. x ∈ X {\\textstyle x\\in X} ![{\textstyle x\in X}](https://wikimedia.org/api/rest_v1/media/math/render/svg/21d7c0406757a1b48249ee3d5577e8d93fbaaa1d) .\
\
  \
In detail, the argument is as follows: since 1 ¯ B L ≥ 1 ¯ B L + 1 ≥ ⋯ ≥ 0 {\\displaystyle {\\bar {1}}\_{B\_{L}}\\geq {\\bar {1}}\_{B\_{L+1}}\\geq \\cdots \\geq 0} ![{\displaystyle {\bar {1}}_{B_{L}}\geq {\bar {1}}_{B_{L+1}}\geq \cdots \geq 0}](https://wikimedia.org/api/rest_v1/media/math/render/svg/fa0c8ec60c4558b5a14906d6561c81c4b381be42) , and ∫ 1 ¯ B L → 0 {\\displaystyle \\int {\\bar {1}}\_{B\_{L}}\\to 0} ![{\displaystyle \int {\bar {1}}_{B_{L}}\to 0}](https://wikimedia.org/api/rest_v1/media/math/render/svg/4fc63eb42046ed8e6ad2ef3f18b1d15a3dca4bb8) , we know that for any small δ , δ ′ \> 0 {\\displaystyle \\delta ,\\delta '>0} ![{\displaystyle \delta ,\delta '>0}](https://wikimedia.org/api/rest_v1/media/math/render/svg/0d08ce3ac26f94f4465d46dd3190100d955485e1) , all large enough L {\\displaystyle L} ![{\displaystyle L}](https://wikimedia.org/api/rest_v1/media/math/render/svg/103168b86f781fe6e9a4a87b8ea1cebe0ad4ede8) satisfies 1 ¯ B L ( x ) < δ {\\displaystyle {\\bar {1}}\_{B\_{L}}(x)<\\delta } ![{\displaystyle {\bar {1}}_{B_{L}}(x)<\delta }](https://wikimedia.org/api/rest_v1/media/math/render/svg/1f5b651dfd4ca6b264a2b5466ef679b85824d47a) everywhere except on a set of size ≥ δ ′ {\\displaystyle \\geq \\delta '} ![{\displaystyle \geq \delta '}](https://wikimedia.org/api/rest_v1/media/math/render/svg/bc98d91f82f319ef339e9efb324803a9c7e1304f) . Thus, lim sup n g n ( x ) n ≤ g ′ ( x ) ( 1 − δ ) + ϵ {\\displaystyle \\limsup \_{n}{\\frac {g\_{n}(x)}{n}}\\leq g'(x)(1-\\delta )+\\epsilon } ![{\displaystyle \limsup _{n}{\frac {g_{n}(x)}{n}}\leq g'(x)(1-\delta )+\epsilon }](https://wikimedia.org/api/rest_v1/media/math/render/svg/bac38dfaf021c469297ff8adef8a3d6e5dbceabe) with probability ≥ 1 − δ ′ {\\displaystyle \\geq 1-\\delta '} ![{\displaystyle \geq 1-\delta '}](https://wikimedia.org/api/rest_v1/media/math/render/svg/9b220bd8a1a4c62fe638e2b92d67e3c0f0dfb52c) . Now take both δ , δ ′ → 0 {\\displaystyle \\delta ,\\delta '\\to 0} ![{\displaystyle \delta ,\delta '\to 0}](https://wikimedia.org/api/rest_v1/media/math/render/svg/d913fa8ee78a36c98a935ae98aaa26daf22f227e) .\
\
Applications\
------------\
\
[edit](https://en.wikipedia.org/w/index.php?title=Kingman%27s_subadditive_ergodic_theorem&action=edit&section=10 "Edit section: Applications")\
\
Taking g n ( x ) := ∑ j \= 0 n − 1 f ( T j x ) {\\displaystyle g\_{n}(x):=\\sum \_{j=0}^{n-1}f(T^{j}x)} ![{\displaystyle g_{n}(x):=\sum _{j=0}^{n-1}f(T^{j}x)}](https://wikimedia.org/api/rest_v1/media/math/render/svg/77bad72c3e16620af8f0b9644059f274a711fde1) recovers Birkhoff's pointwise ergodic theorem.\
\
Taking all g n {\\displaystyle g\_{n}} ![{\displaystyle g_{n}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/177cf6000dd244d8051d352342a8377c0059db0d) constant functions, we recover the Fekete's subadditive lemma.\
\
Kingman's subadditive ergodic theorem can be used to prove statements about [Lyapunov exponents](https://en.wikipedia.org/wiki/Lyapunov_exponent "Lyapunov exponent")\
. It also has applications to [percolations](https://en.wikipedia.org/wiki/Percolation_theory "Percolation theory")\
 and [longest increasing subsequence](https://en.wikipedia.org/wiki/Longest_increasing_subsequence "Longest increasing subsequence")\
.[\[4\]](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#cite_note-4)\
\
### Longest increasing subsequence\
\
[edit](https://en.wikipedia.org/w/index.php?title=Kingman%27s_subadditive_ergodic_theorem&action=edit&section=11 "Edit section: Longest increasing subsequence")\
\
To study the longest increasing subsequence of a random permutation π {\\displaystyle \\pi } ![{\displaystyle \pi }](https://wikimedia.org/api/rest_v1/media/math/render/svg/9be4ba0bb8df3af72e90a0535fabcc17431e540a) , we generate it in an equivalent way. A [random permutation](https://en.wikipedia.org/wiki/Random_permutation "Random permutation")\
 on 1 : n {\\displaystyle 1:n} ![{\displaystyle 1:n}](https://wikimedia.org/api/rest_v1/media/math/render/svg/b62854651e7b5b8766d9b089edce5ed4f3379fa4) is equivalently generated by uniformly sampling n {\\displaystyle n} ![{\displaystyle n}](https://wikimedia.org/api/rest_v1/media/math/render/svg/a601995d55609f2d9f5e233e36fbe9ea26011b3b) points in a square, then find the longest increasing subsequence of that.\
\
Now, define the [Poisson point process](https://en.wikipedia.org/wiki/Poisson_point_process "Poisson point process")\
 with density 1 on \[ 0 , ∞ ) 2 {\\displaystyle \[0,\\infty )^{2}} ![{\displaystyle [0,\infty )^{2}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/9344632df798a9fb7d480004a0c78474c6fc7e28) , and define the random variables M k ∗ {\\displaystyle M\_{k}^{\*}} ![{\displaystyle M_{k}^{*}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/a4e4c95d8c386aab945e4470396c84128d312a54) to be the length of the longest increasing subsequence in the square \[ 0 , k ) 2 {\\displaystyle \[0,k)^{2}} ![{\displaystyle [0,k)^{2}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/103cdd2329ca898d794ec8542b31637a841fce80) . Define the measure-preserving transform T {\\displaystyle T} ![{\displaystyle T}](https://wikimedia.org/api/rest_v1/media/math/render/svg/ec7200acd984a1d3a3d7dc455e262fbe54f7f6e0) by shifting the plane by ( − 1 , − 1 ) {\\displaystyle (-1,-1)} ![{\displaystyle (-1,-1)}](https://wikimedia.org/api/rest_v1/media/math/render/svg/c96b373a30a5cd3f87bba41b65da5fb522ea58a9) , then chopping off the parts that have fallen out of \[ 0 , ∞ ) 2 {\\displaystyle \[0,\\infty )^{2}} ![{\displaystyle [0,\infty )^{2}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/9344632df798a9fb7d480004a0c78474c6fc7e28) .\
\
The process is subadditive, that is, M k + m ∗ ≥ M k ∗ + M m ∗ ∘ T k {\\displaystyle M\_{k+m}^{\*}\\geq M\_{k}^{\*}+M\_{m}^{\*}\\circ T^{k}} ![{\displaystyle M_{k+m}^{*}\geq M_{k}^{*}+M_{m}^{*}\circ T^{k}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/6a5deb8da2b5c0279d245f60a2e13e10f13665c3) . To see this, notice that the right side constructs an increasing subsequence first in the square \[ 0 , k ) 2 {\\displaystyle \[0,k)^{2}} ![{\displaystyle [0,k)^{2}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/103cdd2329ca898d794ec8542b31637a841fce80) , then in the square \[ k , k + m ) 2 {\\displaystyle \[k,k+m)^{2}} ![{\displaystyle [k,k+m)^{2}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/e275dc50688a342938a99aaece47b5ac4e05ce69) , and finally concatenate them together. This produces an increasing subsequence in \[ 0 , k + m ) 2 {\\displaystyle \[0,k+m)^{2}} ![{\displaystyle [0,k+m)^{2}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/e44d3de95ba30c60b440f0cd4058e18d3389d1c6) , but not necessarily the longest one.\
\
Also, T {\\displaystyle T} ![{\displaystyle T}](https://wikimedia.org/api/rest_v1/media/math/render/svg/ec7200acd984a1d3a3d7dc455e262fbe54f7f6e0) is ergodic, so by Kingman's theorem, M k ∗ / k {\\displaystyle M\_{k}^{\*}/k} ![{\displaystyle M_{k}^{*}/k}](https://wikimedia.org/api/rest_v1/media/math/render/svg/4d657c582b44da105bf56eed4ba7308d4fb314b3) converges to a constant almost surely. Since at the limit, there are n \= k 2 {\\displaystyle n=k^{2}} ![{\displaystyle n=k^{2}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/f4f3ed4717329e4c931a9815531ad2feddbe8ea6) points in the square, we have L n ∗ / n {\\displaystyle L\_{n}^{\*}/{\\sqrt {n}}} ![{\displaystyle L_{n}^{*}/{\sqrt {n}}}](https://wikimedia.org/api/rest_v1/media/math/render/svg/c3116c04074daaa2ae7b4f8013c4b19741689ffc) converging to a constant almost surely.\
\
References\
----------\
\
[edit](https://en.wikipedia.org/w/index.php?title=Kingman%27s_subadditive_ergodic_theorem&action=edit&section=12 "Edit section: References")\
\
1.  [↑](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#cite_ref-proof1_1-0 "Jump up")\
     S. Lalley, Kingman's subadditive ergodic theorem lecture notes, [http://galton.uchicago.edu/~lalley/Courses/Graz/Kingman.pdf](http://galton.uchicago.edu/~lalley/Courses/Graz/Kingman.pdf)\
    \
2.  [↑](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#cite_ref-2 "Jump up")\
     Chen. ["Subadditive ergodic theorems"](http://math.nyu.edu/degree/undergrad/Chen.pdf)\
     (PDF). New York University.\
3.  [↑](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#cite_ref-3 "Jump up")\
     Steele, J. Michael (1989). ["Kingman's subadditive ergodic theorem"](https://web.archive.org/web/20060905180629/http://www-stat.wharton.upenn.edu/~steele/Publications/PDF/Steele_AIHPB_1989.pdf)\
     (PDF). _Annales de l'I.H.P. Probabilités et statistiques_. **25** (1): 93–98\. [ISSN](https://en.wikipedia.org/wiki/ISSN_(identifier) "ISSN (identifier)")\
     [1778-7017](https://search.worldcat.org/issn/1778-7017)\
    . Archived from the original on 2006-09-05. Retrieved 2024-01-13.`{{[cite journal](https://en.wikipedia.org/wiki/Template:Cite_journal "Template:Cite journal") }}`: CS1 maint: bot: original URL status unknown ([link](https://en.wikipedia.org/wiki/Category:CS1_maint:_bot:_original_URL_status_unknown "Category:CS1 maint: bot: original URL status unknown")\
    )\
4.  [↑](https://en.wikipedia.org/wiki/Kingman%27s_subadditive_ergodic_theorem#cite_ref-4 "Jump up")\
     Pitman, Lecture 12: Subadditive ergodic theory, [http://www.stat.berkeley.edu/~pitman/s205s03/lecture12.pdf](http://www.stat.berkeley.edu/~pitman/s205s03/lecture12.pdf)\
    \
\
 \
\
Retrieved from "[https://en.wikipedia.org/w/index.php?title=Kingman%27s\_subadditive\_ergodic\_theorem&oldid=1314661162](https://en.wikipedia.org/w/index.php?title=Kingman%27s_subadditive_ergodic_theorem&oldid=1314661162)\
"\
\
[Last edited on 2 October 2025, at 16:23](https://en.wikipedia.org/w/index.php?title=Kingman%27s_subadditive_ergodic_theorem&action=history)\
\
#### Languages\
\
This page is not available in other languages.\
\
![Wikipedia](https://en.wikipedia.org/static/images/mobile/copyright/wikipedia-wordmark-en-25.svg)\
\
*   [![Wikimedia Foundation](https://en.wikipedia.org/static/images/footer/wikimedia.svg)](https://www.wikimedia.org/)\
    \
*   [![Powered by MediaWiki](https://en.wikipedia.org/w/resources/assets/mediawiki_compact.svg)](https://www.mediawiki.org/)\
    \
\
*   This page was last edited on 2 October 2025, at 16:23 (UTC).\
*   Page was rendered with [Parsoid](https://www.mediawiki.org/wiki/Special:MyLanguage/Parsoid "mw:Special:MyLanguage/Parsoid")\
    .\
*   Content is available under [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/deed.en)\
     unless otherwise noted.\
\
*   [Privacy policy](https://foundation.wikimedia.org/wiki/Special:MyLanguage/Policy:Privacy_policy)\
    \
*   [About Wikipedia](https://en.wikipedia.org/wiki/Wikipedia:About)\
    \
*   [Disclaimers](https://en.wikipedia.org/wiki/Wikipedia:General_disclaimer)\
    \
*   [Contact Wikipedia](https://en.wikipedia.org/wiki/Wikipedia:Contact_us)\
    \
*   [Legal & safety contacts](https://foundation.wikimedia.org/wiki/Special:MyLanguage/Legal:Wikimedia_Foundation_Legal_and_Safety_Contact_Information)\
    \
*   [Code of Conduct](https://foundation.wikimedia.org/wiki/Special:MyLanguage/Policy:Universal_Code_of_Conduct)\
    \
*   [Developers](https://developer.wikimedia.org/)\
    \
*   [Statistics](https://stats.wikimedia.org/#/en.wikipedia.org)\
    \
*   [Cookie statement](https://foundation.wikimedia.org/wiki/Special:MyLanguage/Policy:Cookie_statement)\
    \
*   [Terms of Use](https://foundation.m.wikimedia.org/wiki/Special:MyLanguage/Policy:Terms_of_Use)\
    \
*   [Desktop view](https://en.wikipedia.org/w/index.php?title=Kingman%27s_subadditive_ergodic_theorem&mobileaction=toggle_view_desktop)