Furstenberg-Kesten theorem
==========================

  

Consider μμ a [probability measure](javascript:void(0))
[![Mathworld](http://mathworld.wolfram.com/favicon_mathworld.png)](http://mathworld.wolfram.com/ProbabilityMeasure.html)
[![Planetmath](http://planetmath.org/sites/default/files/fab-favicon.ico)](http://planetmath.org/measure)
, and f:M→Mf:M→M a [measure preserving](http://planetmath.org/measurepreserving)
 [dynamical system](javascript:void(0))
[![Mathworld](http://mathworld.wolfram.com/favicon_mathworld.png)](http://mathworld.wolfram.com/DynamicalSystem.html)
[![Planetmath](http://planetmath.org/sites/default/files/fab-favicon.ico)](http://planetmath.org/groupoidcdynamicalsystem)
[![Planetmath](http://planetmath.org/sites/default/files/fab-favicon.ico)](http://planetmath.org/dynamicalsystem)
. Consider A:M→GL(d,𝐑)A:M→GL(d,R), a [measurable](http://planetmath.org/riemannmultipleintegral)
 transformation, where GL(d,R) is the space of [invertible](javascript:void(0))
[![Planetmath](http://planetmath.org/sites/default/files/fab-favicon.ico)](http://planetmath.org/matrixinverse)
[![Planetmath](http://planetmath.org/sites/default/files/fab-favicon.ico)](http://planetmath.org/invertiblelineartransformation)
 [square matrices](javascript:void(0))
[![Mathworld](http://mathworld.wolfram.com/favicon_mathworld.png)](http://mathworld.wolfram.com/SquareMatrix.html)
[![Planetmath](http://planetmath.org/sites/default/files/fab-favicon.ico)](http://planetmath.org/squarematrix)
 of size dd. Consider the multiplicative cocycle (ϕn(x))n(ϕn(x))n defined by the transformation AA.

If log+||A||log+||A|| is [integrable](http://planetmath.org/vectorvaluedfunction)
, where log+||A||\=max{log||A||,0}log+||A||\=max{log||A||,0}, then:

|     |     |     |
| --- | --- | --- |
|     | λmax(x)\=limn1nlog\|ϕn(x)\|λmax(x)\=limn1nlog\|ϕn(x)\| |     |

exists almost everywhere, and λ+maxλ+max is integrable and

|     |     |     |
| --- | --- | --- |
|     | ∫λmax𝑑μ\=limn1n∫log\|ϕn\|dμ\=infn1n∫log\|ϕn\|dμ∫λmaxdμ\=limn1n∫log\|ϕn\|dμ\=infn1n∫log\|ϕn\|dμ |     |

If log+||A\-1||log+||A−1|| is integrable, then:

|     |     |     |
| --- | --- | --- |
|     | λmin(x)\=limn\-1nlog\|ϕ\-n(x)\|λmin(x)\=limn−1nlog\|ϕ−n(x)\| |     |

exists almost everywhere, and λ+minλ+min is integrable and

|     |     |     |
| --- | --- | --- |
|     | ∫λmin𝑑μ\=limn\-1n∫log\|ϕ\-n\|dμ\=supn\-1n∫log\|ϕ\-n\|dμ∫λmindμ\=limn−1n∫log\|ϕ−n\|dμ\=supn−1n∫log\|ϕ−n\|dμ |     |

Furthermore, both λminλmin and λmaxλmax are [invariant](http://mathworld.wolfram.com/Invariant.html)
 for the tranformation ff, that is, λmin∘f(x)\=λmin(x)λmin∘f(x)\=λmin(x) and λmax∘f(x)\=λmax(x)λmax∘f(x)\=λmax(x), for μμ almost everywhere.

This theorem is a direct consequence of Kingman’s subadditive [ergodic theorem](http://planetmath.org/ergodictheorem)
, by observing that both

|     |     |     |
| --- | --- | --- |
|     | log\|ϕn(x)\|log\|ϕn(x)\| |     |

and

|     |     |     |
| --- | --- | --- |
|     | log\|ϕ\-n(x)\|log\|ϕ−n(x)\| |     |

are subadditive sequences.

The results in this theorem are strongly improved by Oseledet’s multiplicative ergodic theorem, or Oseledet’s [decomposition](http://planetmath.org/complementarysubspace)
.

|     |     |
| --- | --- |
| Title | Furstenberg-Kesten theorem |
| Canonical name | FurstenbergKestenTheorem |
| Date of creation | 2014-03-19 22:14:18 |
| Last modified on | 2014-03-19 22:14:18 |
| Owner | Filipe (28191) |
| Last modified by | Filipe (28191) |
| Numerical id | 3   |
| Author | Filipe (28191) |
| Entry type | Theorem |
| Related topic | Oseledet’s decomposition |
| Related topic | multiplicative cocycle |

Generated on Fri Feb 9 21:09:46 2018 by [LaTeXML ![[LOGO]](<Base64-Image-Removed>)](http://dlmf.nist.gov/LaTeXML/)