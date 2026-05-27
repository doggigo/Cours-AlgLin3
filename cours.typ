#import "@local/utils:0.1.0": *
#import "@local/doc_fac:0.1.0" as theme_colors
#import "@local/doc_cours_nb:0.1.0" as theme_nb

#let theme_default = "colors"

#let theme_name = sys.inputs.at("theme", default: theme_default)


#let theme = if theme_name == "colors" { theme_colors } else { theme_nb }

#let theorem = theme.theorem
#let corollary = theme.corollary
#let lemma = theme.lemma
#let property = theme.property
#let proposition = theme.proposition
#let exercice = theme.exercice
#let example = theme.example
#let notation = theme.notation
#let remark = theme.remark
#let method = theme.method
#let definition = theme.definition
#let vocabulary = theme.vocabulary
#let proof = theme.proof

#let only-thms = sys.inputs.at("only-thms", default: "false") == "true"

#show: theme.doc_fac.with(
  title: "Cours AlgLin3",
  numbering: "I. 1. 1. a) i)",
  show-examples: not only-thms,
  show-exercises: not only-thms,
  show-proofs: not only-thms,
  page-numbering: "1",
)

#outline()

= Dualité

$KK$ désigne un corps $(KK = RR "ou" CC)$, $E$ sera un $KK-$ev
== Dual

#definition[
  On appelle forme linéaire sur $E$ toute application linéaire de $E$ à valeur dans $KK$.

  On appelle *dual* de $E$, noté $E^*$ (ou $E^checkmark$) le $KK$-ev formé des formes linéaires sur $E$, $E = Lin(E, KK)$.
]

#example[
  + L'application nulle : $0 : application(E, KK, x, 0)$
  + $ application(RR^3, RR, (x,y,z), 3x-y+2z) $ est une fome linéaire sur $RR^3$
  + L'évaluation d'un polynôme en $a in KK$ :
    $ e v_a : application(KK[X], KK, P, P(a)) $ est une forme linéaire sur $KK[X]$
  + Pour $E = C^0([0,1],RR)$, $application(E, RR, f, integral_0^1 f(t) d t)$ est une forme linéaire dans $E$.
  + $E = {(u_n) in KK^NN | (u_n) --> l in KK}$, alors
  $application(E, KK, (u_n)_(n in NN), lim_(n -> + infinity) u_n)$ est une forme linéaire
]

#remark[
  Toute forme linéaire sur $RR^3$ est de la forme $a x + b y + c z$ avec $(a,b,c) in RR^3$

  Ainsi $(RR^3)^* = {f : (x,y,z) |-> a x + b y + c z | a,b,c in RR}$
]

#proof[
  Soit $(e_1,e_2,e_3)$ la b.c. de $RR^3$, et $(a,b,c) = (f(e_1),f(e_2),f(e_3))$ alors puisque $(x,y,z) = x e_1 + y e_2 + z e_3$, $f(x,y,z) = a x + b y + c z$
]

#property[
  Si $E$ est de dimension finie alors $E^*$ aussi et ils sont de même dimension.
]

#proof[
  $dim(Lin(E, KK) = dim E cdot dim KK = dim E)$
]

== Hyperplans

#definition[
  On appelle hyperplan de $E$ le noyau d'une forme linéaire non-nulle sur $E$. Si $phi in E^* without {0_(E^*)}$, on dira que $H = Ker(phi)$ est l'hyperplan d'équation $phi(x) = 0$
]

#example[
  + $H = {A in M_n (KK) | Tr(A) = 0}$ est un hyperplan de $M_n (KK)$. Tr est non-nulle : $Tr(I_n) = n$ par ex
  + $H = {(x,y,z) in RR^3 | 3 x - y + 2 z = 0}$ est un hyperplan.
  + $H = {P in KK[Z] | P(1) = 0}$ est un hyperplan car l'application n'est pas nulle.
]

#property[
  Soit $H$ un sous-espace vectoriel de $E$. Les assertions suivantes sont équivalentes :
  + $H$ est un hyperplan de $E$
  + Il existe une droite vectorielle $D$ telle que $E = D osum H$
  + Si $E$ est de dimension finie, $dim(H) = dim(E)-1$
]

#proof[
  - $underline(a => b)$ :  $H = ker(phi)$ avec $phi in E^* without {t |-> 0}$. Alors $exists u in E. phi(u) != 0$. Posons $D = K u = Vect(u)$ et montrons que $E = H osum D$.
    Si $x in H inter D$. Alors $x = lambda u, lambda in KK$ et $phi(x) = phi(lambda u) = lambda phi(u) = 0$. Donc $lambda = 0$ càd $x = 0$. Maintenant soit $x in E$, notons $alpha = phi(x)/phi(u) in KK$ et posons $h = x - alpha u$. Alors $phi(h) = phi(x) - alpha pi(u) = 0$ donc $h in H$ et $x = h + alpha u$. D'où la somme directe.
  - $underline(b => a)$ : Soit $D = K v = Vect(v), v != 0$ telle que $E = H osum D$.
    $forall x in E, x = underbrace(h_x, in H) + underbrace(lambda_x v, in D), quad lambda_x in KK$
    On pose $phi(x) = lambda x$. $phi : E -> KK$. Il reste à montrer que $phi$ est linéaire. $phi(x)$ est l'unique scalaire tel que $x - phi(x)v in H$.

    Soit $mu in KK$, $(mu x + y) - (mu phi(x) + phi(y))v = mu underbrace((x - phi(x) v), in H) + underbrace((y - phi(y) v), in H)$. Ainsi $(mu x + y) - (mu phi(x) + phi(y)) v in H$. D'où $phi(mu x + y) = mu phi(x) + phi(y)$ et $phi$ est linéaire.
]

== Base duale
Dans ce paragraphe, $E$ est de dimension finie.

Soit $EEE = (e_1, ..., e_n)$ une base d e $E$.

Pour $j in [|1,n|]$, on définit $e_j^* : E -> K$ la forme linéaire définie par $e_j^* (e_i) = delta_(i j)$

#proposition[
  La famille $EEE^* = (e_1^*, dots, e_n^*)$ est une base de $E^*$ appelée base duale de $EEE$.
]

#proof[
  Il suffit de montrer que $EEE^*$ est libre. Soit $(alpha_j)_(1 <= j <= n)$ une une famille de scalaires.

  Alors soit la somme : $sum_(j = 1)^n alpha_j e_j^* = 0$. Pour $i in [|1,n|]$, $(sum_(j = 1)^n alpha_j e_j^*)(e_i) = 0 = alpha_i$ d'où $EEE^*$ libre càd base.
]

#proposition("Changement de bases")[
  Soit $EEE,FFF$ deux bases de $E$, $P = P_EEE^FFF$, alors la matrice de passage de $EEE^*$ à $FFF^*$ est :
  $
    Q = transp(P^(-1))
  $
]

#proof[
  $EEE = (e_1, dots, e_n), FFF = (f_1, dots, f_n), P = [p_(i j)]_(1<=i,j<=n)$.

  $forall k in [|1,n|], f_k = sum_(l=1)^n p_(l k) e_l$.

  Notons $Q = [q_(i j)]_(1 <= i,j <= n) "et" f_j^* = sum_(i = 1)^n q_(i j) e^*_i$ pour tout $j in [|1,n|]$.

  $delta_(j k) = f_j^*(f_k) = sum_(i = 1^n) q_(i j) e_i^* (sum_(l = 1)^n p_(l k) e_l) = sum_(i = 1)^n sum_(l = 1)^n q_(i j) p_(l k) e_i^*(e_p) = sum_(i = 1)^n q_(i j) p_(i k)$.

  Ce terme correspond au coefficient de la $j$-ième ligne, $k$-ième colonne de la matrice $transp(Q)P$.

  Donc $transp(Q)P = I_n$ càd : $Q = transp(P^(-1))$
]

#method("Trouver une base duale/antéduale")[
  En connaissant la base duale de la base canonique, on peut calculer la base duale de $(f_i)$ en prenant $M^* = transp(M^(-1))$ avec $M = Mat_((f_i),"b.c")(Id)$

  #v(.5em)

  De même, pour trouver la base antéduale de $f_i^*$, on peut prendre la transposée de $Mat_((f_i^*),"b.c.")(Id)$
]

#method("2nde méthode")[
  On a : $ e_i^*(x) = 1/det(M) det(e_1, dots, e_(i-1), x, e_(i+1), dots, e_n) $

  qui est bien une application et vaut $delta_(i j)$ c'est-à-dire $cases(1 "si" x = e_i, 0 "sinon")$
]

#corollary[
  Toute base de $E^*$ est une base duale. Autrement dit, si $EEE'$ est une base de $E^*$, il existe une base $EEE$ de $E$ telle que $EEE' = EEE^*$ la base duale de $EEE$.

  $EEE$ est appelée base préduale (ou antéduale) de $EEE'$
]

#proof[
  Soit $FFF$ une base de $E$, $FFF^*$ sa base duale. Notons $Q$ la matrice de passage de $FFF^*$ à $EEE'$ et $P = transp(Q^(-1))$. Appelons $EEE$ la base de $E$ telle que $P$ soit la matrice de passage de $FFF$ à $EEE$. La matrice de passage de $FFF^*$ à $EEE^*$ est $transp(P^(-1)) = Q$ (via la prop. précédente) donc $EEE' = EEE^*$
]

#corollary[
  Soit $E$ de dimension $n$.
  + Tout sev de $E$ de dimension $n-p$ avec $1 <= p <= n$ est l'intersection de $p$ hyperplans.
  + soit $(phi_1, dots, phi_p)$ une famille de $p$ formes linéaires non-nulles et $G = biginter_(i = 1)^n Ker(phi_i)$, alors $dim(G) = n - dim(Vect(phi_1, dots, phi_n))$.
]

#proof[
  + Soit $F$ un sev de $E$ de dimension $n - p$ de base $(e_i)_(1<= k <= n-p)$ complétée en $(e_i)_(1 <= k <= n)$ base de $E$. Alors $F = underbrace(biginter_(i = n - p + 1)^n Ker(e_i^*), p "hyperplans")$
  + Supposons d'abord que $(phi_i)_(1<= i <= p)$ est libre. On la complète en une base $(phi_1, dots, phi_p, dots, phi_m)$ de $E^*$ et on note $(e_i)_(1<=i<=n)$ la base antéduale de $(phi_i)$. Alors $G = biginter_(i = 1)^p Ker(phi_i) = biginter_(i = 1)^p Ker(e_i^*) = Vect(e_(p+1), dots, e_n)$ et $dim G = n-p$
  + Si $(phi_1, dots, phi_p)$ est liée, soit $Phi = Vect(phi_1, dots, phi_p), quad d = dim Phi$. Sans perdre de généralités (quitte à renumérotter), on peut supposer que $(phi_1, dots, phi_d)$ est une base de $Phi$.
  Pour $j in [|d+1,p|]$, $phi_j = sum_(i=1)^d lambda_i^j phi_i, quad lambda_i^j in K$.
  $ biginter_(i=1)^d Ker(phi_i) = biginter_(i=1)^p Ker(phi_i) $ et par ce qui précède, $dim(G) = n-d$.
]

== bidual

#definition[
  Pour un $KK$-ev, le dual de $E^*$ est noté $E^(**)$ et appelé bidual de $E$.
]
#proof("de la linéarité")[
  Considérons l'application :
  $Phi : application(E, E^(**), x, Phi(x) : application(E^*, K, phi, Phi(x)(phi)=phi(x)))$

  Montrons que $Phi$ est bien définie, il faut montrer que $Phi(x)$ est linéaire.

  $forall phi,psi in E^*, Phi(x)(lambda phi + psi) = (lambda phi + psi) = lambda phi(x) + psi(x) = lambda Phi(x)(phi) + Phi(x)(psi)$
]

#theorem[
  Si $E$ est #underline([de dimension finie]), $Phi$ est un isomorphisme.
]

#proof[
  + $Phi$ est linéaire : $forall x,y in E, forall lambda in KK, underbrace(Phi(lambda x + y), in E^(**))(phi) = phi(lambda x + y) = lambda phi(x) + phi(y) = lambda Phi(x)(phi) + Phi(y)(phi)$. Donc $Phi(lambda x + y) = lambda phi(x) + phi(y) = (lambda Phi(x) + Phi(y))(psi)$.

  + $Phi$ est bijective : comme $E^(**)$ de dimenion finie, il suffit de montrer que $Phi$ est injective. Soit $x in Ker(Phi)$. Phi(x) est l'application nulle. Donc pour tout $phi in E^*$, $Phi(x)(phi) = phi(x) = 0$ et donc $x = 0_E$. En effet, en notant $x = sum_(i = 1)^n x_i e_i$, $(e_i)$ base de $E$. Par contraposée, supposons $x != 0_E$, i.e. $exists x_(i_0) != 0$ avec $i_0 in [|1,n|]$. Et $x_(i_0) = e_(i_0)^* (x)$ donc $e_(i_0)^* (x) != 0$ et $e_(i_0)^* in E^*$. $Phi(x)(e_(i_0)^*) != 0$.
]

#remark[
  Si $E$ n'est pas de dimension finie, on peut montrer que $Phi$ reste injective, mais n'est plus surjective.
]

#remark("À l'oral")[
  Si $(phi_i)$ base de $(E^(*))$, $(phi_i^*)~> (Phi^(-1)(phi_n^*))$ est la base antéduale de $(phi_i)$
]


= Espaces Euclidiens
Dans ce chapitre, nous travaillerons uniquement sur des $RR$-ev.

== Produit scalaire
#definition("Forme bilinéaire")[
  Soit $E$ un $RR$-ev. On appelle forme bilinéaire sur $E$ une application $f : E^2 -> RR$ linéaire à chaque variable. C'est-à-dire,
  - $forall x, x', y, in E, forall lambda in RR, f(lambda x + x', y) = lambda f(x,y) + f(x',y)$
  - $forall x,y,y' in E, forall mu in RR, f(x,mu y + y') = mu f(x,y) + f(x,y')$
]

#remark[
  Notons $BBB(E)$ l'ensemble des formes bilinéaires sur $E$. $BBB(E)$ est un $RR$-ev
]

#exercice[
  Le prouver
]

#remark[
  Se donner une forme bilinéaire sur $E$ équivaut à se donner une application linéaire de $E$ sur $E^*$.
]
#proof[
  Considérons
  $
    L : application(BBB(E), Lin(E, E^*), f, L(f) : application(E, E^*, y, L(f)(y) : application(E, RR, x, f(x,y))))
  $
  $L$ est bien définie.
  + $forall y in E, L(f)(y)$ est une forme linéaire :
    $forall x,x' in E, forall lambda in RR, L(f)(y)(lambda x+x') = f(lambda x + x',y) = lambda f(x,y) + f(x',y) = lambda L(f)(y)(x) + L(f)(y)(x')$
  + $L(f)$ est linéaire :

    $
      forall y,y' in E, forall lambda in RR, forall x in E : underbrace(L(f)(lambda y + y'), in E)(x)= f(x,lambda y + y') \
      = lambda f(x,y) + f(x,y') = lambda L(f)(y)(x) + L(f)(y')(x)
    $
]

#theorem[
  $
    L : application(BBB(E), Lin(E, E^*), f, L(f) : application(E, E^*, y, L(f)(y) : application(E, RR, x, f(x,y))))
  $
  Est un isomorphisme.
]
#proof[
  - $L$ est linéaire, $forall f,g in BBB(E), forall lambda in RR, forall x,y in E$ :
    $
      L(lambda f + g)(y)(x) = (lambda f + g)(x,y) = lambda f(x,y) + g(x,y) = lambda L(f)(y)(x) + L(g)(y)(x)
    $
  - $L$ est bijective. Considérons
    $
      psi : application(Lin(E, E^*), BBB(E), h, psi(h):application(E^2, RR, (x,y), psi(h)(x,y) = h(y)(x)))
    $
    $psi$ est l'application réciproque de $L$ :

    Montrons que $L compose psi = Id_(Lin(E, E^*))$ et $psi compose L = Id_(BBB(E))$

    (#underline("Remarque :") $psi(h)$ est bien une forme bilinéaire sur $E$)

    $
      forall h in LL(E, E^*), forall x,y in E, [L compose psi(h)](y) = L(psi(h))(y)(x) = psi(h)(x,y) = h(y)(x)
    $

    Ainsi : $[L compose psi](h) = h$

    Pour l'autre côté :
    $
      forall f in BBB(E), forall x,y in E
      [psi compose L](f)(x,y) = L(f)(y)(x) = f(x,y)
    $
    D'où $[psi compose L](f) = f$. $phi$ est bien inversible donc un isomorphisme.
]

#definition("Produit scalaire")[
  Une *forme bilinéaire* $f : application(E^2, RR, (x,y), f(x,y))$ est un produit scalaire sur $E$ si :
  - $f$ est *symétrique* : $forall x,y in E : f(x,y) = f(y,x)$
  - $f$ est *définie positive* : $forall x in E$, $f(x,x) >= 0$ et $f(x,x) = 0 <==> x = 0$
]

#notation[
  si $f$ est un produit scalaire sur $E$, on notera $f(x,y) = scal2(x, y)$
]

#definition("Espaces Euclidiens, Préhilbertiens")[
  Un $RR$-ev muni d'un produit scalaire est dit espace Préhilbertien réel. Si, de plus, il est de dimension finie, on dit que c'est un *espace Euclidien*
]

#example[
  + $RR^n$ muni du produit scalaire usuel
    $
      scal2(., .) : (vec(x_1, vdots, x_n),vec(y_1, vdots, y_n)) |-> sum_(i = 1)^n x_i y_i
    $
    est un espace Euclidien car
    c'est bien une forme bilinéaire symétrique définie positive

  + $C^0([0,1],RR)$ est un espace Préhilbertien réel pour le produit scalaire $ scal2(., .) : (f,g) |-> integral_0^1 f(x)g(x)d x $
    C'est une forme bilinéaire symétrique définie positive (par positivité de l'intégrale et critère de nullité)
  + $MM_n (RR)$ muni du produit scalaire usuel $ scal2(., .) : (A,B) |-> Tr(transp(A)B) $
    C'est bien une forme bilinéaire symétrique. Montrons que c'est défini positif :
    Soit $A = (a_(i,j))_(1<=i,j<=n), B = (b_(i,j))_(1<=i,j<=n), transp(A)B = (c_(i,j))_(1<=i,j<=n)$,
    Alors $c_(i,j) = sum_(k = 1)^n a_(k i) b_(k j)$

    Donc $Tr(transp(A)B) = sum_(i = 1)^n c_(i i) = sum_(i = 1)^n sum_(j = 1)^n a_(k i)b_(k i) = sum_(1<=i,j<=n)a_(k i) b_(k i)$

    Ainsi $scal2(A, A) = Tr(transp(A)A) = sum_(i,k=1)^n a_(k i)^2 >= 0$ et $scal2(A, A) = 0 <==> forall i,k in [|1,n|] : a_(k,i)^2 = 0 <==> A = 0$
]

Puisque pour tout $x in E$, $scal2(x, x) >= 0$, on note $norm(x) = sqrt(scal2(x, x))$

#remark[
  - $norm(x) = 0 <==> x = 0_E$
  - $forall lambda in RR, norm(lambda x) = sqrt(scal2(lambda x, lambda x)) = sqrt(lambda^2 scal2(x, x)) = |lambda|norm(x)$
]

#proposition("Formules de polarisation")[
  $forall x,y in E :$
  $
    scal2(x, y) & = 1/2 (norm(x + y)^2 - norm(x)^2 - norm(y)^2) \
                & = 1/4 (norm(x + y)^2 - norm(x - y)^2)
  $

  On a donc une relation entre la norme et le produit scalaire
]

#proof[
  + $
      norm(x + y) = scal2(x+y, x+y) & = scal2(x, x+y) + scal2(y, x+y)
                                      = scal2(x, x) + scal2(x, y) + scal2(y, x) + scal2(y, y) \
                                    & = norm(x)^2 + 2scal2(x, y) + norm(y)^2
    $
  ce qui donne la première formule en isolant $scal2(x, y)$

  + $
      cases(norm(x + y) = norm(x)^2 + 2 scal2(x, y) + norm(y), norm(x-y) = norm(x)^2 - 2 scal2(x, y) + norm(y)^2)
    $
    On a donc le résultat en sommant et isolant $scal2(x, y)$
]

#corollary("Identité du parallélogramme")[
  $forall x,y in E$ : $norm(x + y)^2 + norm(x-y)^2 = 2 (norm(x)^2 + norm(y)^2)$
]

#theorem("Inégalité de Cauchy-Schwarz")[
  Soit $E$ un espace préhilbertien réel. Alors
  $forall x,y in E :$
  $
    abs(scal2(x, y)) <= norm(x)norm(y)
  $
  avec égalité ssi $(x,y)$ liée.
]

#proof[
  Si $x = 0$ ou $y = lambda x$, on a égalité :
  $scal2(x, lambda x) = lambda norm(x)^2$

  Supposons maintenant $(x,y)$ libre. Soit $lambda in RR$.

  $norm(x + lambda y)^2 = scal2(x+lambda y, x+lambda y) = scal2(x, x+lambda y) + lambda scal2(y, x+lambda y) = scal2(x, x) + lambda scal2(x, y) + lambda^2 scal2(y, y) + lambda scal2(x, y) = norm(x)^2 + 2lambda scal2(x, y) + norm(y)^2$
  C'est un polynôme de degré 2 en lambda qui ne s'annule pas, car à coefficients positifs. Ainsi son déterminant est $<= 0$. Donc :
  $Delta = 4 scal2(x, y)^2 - 4 norm(x)norm(y) <= 0 <=> abs(scal2(x, y)) <= norm(x)norm(y)$

  D'où l'inégalité.
  Montrons que si l'on a égalité, $y = lambda x$.

  Supposons $abs(scal2(x, y)) = norm(x)norm(y)$. Posons $alpha = scal2(x, y)/norm(x)^2$ (on suppose que $x !=0$ donc $norm(x) != 0$)

  Ainsi :
  $scal2(y-alpha x, y - alpha x) = norm(y - alpha x)^2 = norm(y)^2 - 2alpha scal2(x, y) + alpha^2 norm(x) = norm(y)^2- 2 scal2(x, y)^2/norm(x^2) + scal2(x, y)^2/norm(x)^2 = norm(y)^2 - scal2(x, y)^2/norm(x)^2$.
  Or par hypothèse : $norm(y)^2 = scal2(x, y)^2/norm(x)^2$ donc $norm(y - alpha x) = 0$ càd $y = alpha x$
]

#corollary("Inégalité de Minkowski")[
  Soit $E$ un espace préhilbertien réel.

  Pour tout $x,y in E$ : $norm(x + y) <= norm(x) + norm(y)$

  avec égalité ssi $x,y$ sont positivement liés i.e. $x = 0$ ou $x = lambda y$ avec $lambda in RR^+$
]
#proof[
  $norm(x + y)^2 = norm(x)^2 + 2 scal2(x, y) + norm(y)^2 <=^"C-S" norm(x^2) + norm(y)^2 + 2 norm(x)norm(y) = (norm(x)+norm(y))^2$

  Par positivité de la norme :
  $
    norm(x + y) <= norm(x) + norm(y)
  $

  Si $x = 0$, facile
  Si $y = lambda x$ avec $lambda in RR$ :
  $norm(x+y) = (lambda+1) norm(x)$ d'où l'égalité.

  Réciproquement, si on a égalité, on a le cas d'égalité de Cauchy-Schwarz + $abs(scal2(x, y)) = scal2(x, y)$. D'où la liaison positive.
]

#corollary[
  L'application $norm(.) : E -> RR$ est une norme, dite euclidienne, sur E.

  On appelle Espace de Hilbert réel tout Espace Préhilbertien complet pour sa norme euclidienne.
]

#remark("Rappel sur la complétude")[
  $(F,norm(.))$ est complet si toute suite de Cauchy dans $F$ y converge pour $norm(.)$.
]

#remark[
  Si $x,y$ deux vecteurs non-nuls de $E$, l'inégalité de Cauchy-Schwarz donne :
  $
    abs(scal2(x, y))/(norm(x)norm(y)) <= 1
  $
  Donc $exists! theta in [0,pi]$ tel que $cos theta = scal2(x, y)/(norm(x)norm(y))$. $theta$ est dit angle (non-orienté) entre les vecteurs $x$ et $y$.
]

#pagebreak()

== Réduction de Gauss
Donnons-nous un $RR$-ev muni d'une base $(e_1,dots,e_n)$. Soient $x = sum_(i = 1)^n x_i e_i, y = sum_(i = 1)^n y_i e_i$

Soit $f$ une forme #underline("bilinéaire") sur $E$.

Alors :
$
  f(x,y) = f(sum_(i=1)^n x_i e_i,sum_(i=1)^n y_i e_i) = sum_(i=1)^n x_i f(e_i, sum_(j=1)^n y_j e_j) = sum_(i=1)^n sum_(j=1)^n x_i y_j f(e_i,e_j)
$

Si on note $a_(i j) = f(e_i,e_j)$ :
$
  f(x,y) = sum_(i,j=1)^n a_(i j)x_i y_j
$

Maintenant, si $f$ est symétrique :
$
  a_(i j) = f(e_i, e_j) = f(e_j, e_i) = a_(j i)
$
Donc $f(x,x) = underbrace([sum_(i = 1)^n a_(i i)x_i^2], "terme carré") + underbrace([2 sum_(1 <= i < j <= n) a_(i j) x_i x_j], "terme rectangle")$

Donc se donner une norme euclidienne revient à se donner un polynôme homogène de degré 2 en les $x_i$, $i = 1 ... n$ (pourvu que $f$ soit définie positive).

En particulier, $norm(lambda x)^2 = lambda^2 norm(x)^2 quad forall lambda in RR$

#method("Polarisation")[
  La forme polaire $(f(x,y))$ d'une forme bilinéaire symétrique s'obtient à partir de la forme quadratique en #underline(["polarisant les monômes"]).
  + Les termes carrés $a_(i i) x_i^2$ deviennent $a_(i i)x_i y_i$
  + Les termes rectangles $a_(i j)x_i x_j$ deviennent $1/2 (a_(i j) x_i y_j + a_(j i) x_j y_i)$

]

#example[
  $E = RR^3, thick f(x,x) = x_1^2 + 2x_2^2 + 3x_3^2 + 4 x_1 x_2 + x_1 x_3$

  Soit $x = (x_1,x_2,x_3)$, $y = (y_1,y_2,y_3)$

  $
    f(x,y) & = x_1 y_1 + 2 x_2y_2 + 3x_3y_3 + 1/2 ( 4 (x_1 y_2 + x_2 y_1) + (x_1y_3 + x_3y_1)) \
           & = x_1 y_1 + 2 x_2y_2 + 3x_3y_3 + 2 (x_1y_2 + x_2 y_1) + 1/2 (x_1 y_3 + x_3 y_1)
  $
]

La réduction de Gauss est un algorithme permettant de décomposer tout polynôme homogène de degré $2$ en somme de carrés de formes linéaires indépendantes. Elle repose sur les identités :
$
  cases(
    a^2 + 2a b = (a+b)^2 - b^2 quad & (A),
    a b = 1/4 (a+b)^2 - 1/4 (a-b)^2 quad & (B)
  )
$

On utilisera, dans ce chapitre, majoritairement $(A)$. $(B)$ servira surtout plus tard.

Il faut choisir en priorité les termes carrés, et si possible de coefficient $+-1$. Voir les exemples

#example[
  $E = RR^3, thick (e_1,e_2,e_3) "la b.c."$, et $ f(x,x) = x_1^2 + 2 x_2^2 + 5 x_3^2 + 2x_1x_2 - 4x_2x_3 $

  Choisissons le terme $x_1^2$

  Alors $ f(x,x) & = (x_1^2 + 2x_1x_2) + 2x_2^2 + 5 x_3^2 - 4x_2x_3 \
         & =^((A)) [(x_1+x_2)^2 - x_2^2] + 2x_2^2 + 5x_3^2 - 4x_2x_3 \
         & = (x_1+x_2)^2 + x_2^2 + 5x_3^2 - 4x_2x_3 $
  Choisissons le terme $x_2^2$
  Alors $ f(x,x) & = (x_1 + x_2)^2 + (x_2^2 - 4 x_2 x_3) + 5 x_3^2 \
         & =^((A)) (x_1 + x_2)^2 + [(x_2-2x_3)^2 - 4x_3^2] + 5x_3^2 \
         & = (x_1 + x_2)^2 + (x_2 - 2x_3)^2 + x_3^2 >= 0 $

  $f(x,x) = 0 <==> cases(x_1 + x_2 = 0, x_2 - 2x_3 = 0, x_3 = 0) <==> x = (0,0,0)$

  $f$ est un produit scalaire sur $RR^3$.

  On n'aura pas besoin de prouver que $f(x,x) = 0 => x = 0$ par véracité de l'algorithme.


  Les formes linéaires obtenues sont indépendantes. Posons $ l_1(x) = x_1 + x_2, & "soit" l_1 = e_1^* + e_2^* \
  l_2(x) = x_2 - 2x_3 & "soit" l_2 = e_2^* - 2e_3^* \
         l_3(x) = x_3 & "soit" l_3 = e_3^* $

  $(l_1,l_2,l_3)$ est libre car $det(l_1, l_2, l_3) = 1 != 0$, d'où $(l_1,l_2,l_3)$ base de $(RR^3)^*$
]

#example[
  $E = RR^3, x = (x_1,x_2, x_3), quad f(x,x) = x_1 x_2 + x_1 x_3 + x_2 x_3$

  Choisissons le terme $x_1 x_2$

  Alors $ f(x,x) & = underbrace((x_1 + x_3), a)underbrace((x_2+x_3), b) - x_3^2 \
         & =^((B))1/4 (x_1 + x_2 + 3x_3)^2 - 1/4 (x_1 + x_2 + 2x_3)^2 - 1/4 (x_1 - x_2)^2 - x_3^2 $
  n'est pas positive, $f((-2,0,1),(-2,0,1)) = -1-1 = -2 < 0$ donc $f$ n'est pas un produit scalaire.

  Si on pose $l_1 = e_1^* + e_2^*, l_2 = e_1^* - e_2^*, l_3 = e_3^*$, alors $(l_1,l_2,l_3)$ est libre.
]

#example[
  $E = RR^3, quad x = (x_1,x_2,x_3)$

  $
    f(x,x) & = underbracket(x_1^2) + 5x_2^2 + 2x_3^2 + 4x_1x_2 - 2x_1x_3 - 2x_2x_3 \
           & = (x_1^2 + 4x_1x_2 - 2x_1x_3) + 5x_2^2 + 2x_3^2 - 2x_2x_3 \
           & = [x_1 + 2x_1(2x_2 - x_3)] + 5x_2^2 + 2x_3^2 - 2x_2x_3 \
           & =^((A)) [(x_1 + 2x_2 - x_3)^2 - (2x_2 - x_3)^2] + 5x_2_2x_3^2 - 2x_2x_3 \
           & = (x_1 + 2x_2 - x_3)^2 + x_2^2 + x_3^2 + 2 x_2 x_3 \
           & = (x_1 + 2x_2 - x_3)^2 + (x_2 + x_3)^2 >= 0
  $

  Si on pose $l_1 = e_1^* + 2e_2^* - e_3^*, l_2 = e_2^* + e_3^*$.
  $(l_1, l_2)$ est libre, mais ne forme pas une base de $E^*$, c'est-à-dire que $f(x,x) = 0$ est une équation à 3 inconnues et 2 équations, donc admet une infinité de solutions (Cramer etc..), ainsi $f$ n'est pas un produit scalaire.
]

#proposition("Réduction de Gauss")[
  Soit $E$ un $KK$-ev de dimension finie,
  alors il existe un algorithme permettant de décomposer toute forme quadratique sur $E$ en une combinaison linéaire de carrés de formes linéaires.
]

#method("Réduction de Gauss")[
  Soit $E$ un $KK$-ev, $f in BBB(E)$. L'algorithme de Gauss s'effectue de cette manière :
  + Se ramener à $f(x,x) = sum_(i = 1)^n a_(i i)x_i^2 + 2 sum_(1 <= i < j <= n) a_(i j) x_i x_j$ avec $a_(i,j) = f(e_i,e_j)$
  + Choisir un terme, de préférence carré s'il existe, sinon rectangle.
    - Si le terme est un carré $a x_i^2$ rassembler tous les $x_i$ sous la forme : $ a x_i^2 + 2 x_i L(x_1,dots,x_(i-1),x_(i+1),x_n) = a[x_i^2 + (2x_i L)/a] $
      avec $L$ forme linéaire ne dépendant pas de $x_i$, $q$ forme bilinéaire n'en dépendant pas non plus.

      Puis remarquer l'identité $(A)$ :
      $ a[x_i^2 + (2x_i L)/a] = a[(x_i + L/a)^2 - (L/a)^2] = a(x_i+L/a)^2 - L^2/a $ et enfin, développer la partie négative

    - Si le terme est un rectangle $x_i x_j$, on cherche à isoler ces deux variables dans une expression de la forme $x_i x_j + alpha x_i + beta x_j$
      + Factoriser sous la forme : $x_i x_j + alpha x_i + beta x_j = (x_i + beta)(x_j + alpha) - alpha beta$
      + Utiliser l'identité (B) : $a b = 1/4 (a + b)^2 - 1/4 (a - b)^2$ puis continuer
  + Répéter sur les termes qui ne sont pas isolés.

] <methode_reduction_gauss>

#proof([Pt. 1 : Énonciation de la récurrence et cas avec terme carré])[
  La démonstration se fait par récurrence sur $n = dim E$.

  On suppose que $f$ est une forme bilinéaire symétrique non-nulle.
  + Si $n = 1, f(x,x) = a x^2, a in RR^*$, rien à dire.
  + Supposons que pour tout $p < n$, on ait un algorithme permettant de décomposer tout polynôme de degré 2 sur un espace de dimension $p$ en une combinaison linéaire de carrés de formes linéaires indépendantes.

    Soit $E$ de dimension $n$, muni d'une base $(e_i)_(1<=i<=n)$ et d'une forme bilinéaire symétrique non-nulle. Soit $x = sum_(i = 1)^n x_i e_i$

    + Supposons que $f(x,x)$ possède un terme carré que l'on peut supposer être $a x_1^2, a in RR^*$
      $f(x,x) = a x_1^2 + x_1 L(x_2, dots, x_n) + f_1 (x_2, dots, x_n)$ où $L$ est une forme linéaire en $x_2, dots, x_n$ et $f_1$ est un polynôme homogène de degré 2 en $x_2, dots x_n$.

      $
        f(x,x) & = a[x_1^2 + 2x_1 L(x_2,dots,x_n)/(2a)] + f_1 (x_2,dots,x_n) \
               & =^((A)) a[(x_1 + L(x_1, dots, x_n)/(2a)) - L(x_2, dots,x_n)^2/(4 a^2)] + f_1(x_2,dots,x_n) \
               & = a(x_1 + L(x_2, dots,x_n)/(2a))^2 + q(x_2, dots, x_n) quad "où" q(x_1,dots,x_n) \
               & = -L(x_2,dots,x_n)^2/(4 a) + f(x_2,dots,x_n)
      $
      c'est un polynôme de degré 2 où n'apparaît pas $x_1$

      On applique l'hypothèse de récurrence à $Vect(e_2, dots, e_n)$ muni de $q$ si $q != 0$. Rq : si $q = 0$, on a fini.

      On a : $q(x_2, dots, x_n) = sum_(i =2)^r a_i l_i^2 (x_2,dots,x_n)$ où $(l_2, dots,l_r)$ est une famille libre de $Vect(e_2, dots, e_n)^*$.

      Si $x = sum_(i = 1)^n x_i e_i in E$, notons $phi_j(x_1,dots,x_n) = phi_j (x_1,dots,x_n) = phi_j (x_2,dots,x_n)$, pour $j = 2,...,r$ et $phi_1 (x_1,dots,x_n) = x_1 + L(x_2, dots, x_n)/(2 a)$

      $f(x,x) = a phi_1^2(x_1, dots, x_n) + sum_(j = 2)^r a_j phi_j (x_1,dots,x_n)^2$. Il reste à montrer que $(phi_1, dots, phi_r)$ est libre dans $E^*$. Soit l'équation $sum_(i = 1)^r lambda_i phi_i = 0$. En particulier $sum_(i=1)^r lambda_i phi_i (e_1) = lambda_1 phi_1(e_1) = lambda_1 = 0$.

      Pour $j = 2, dots, r, sum_(i = 1)^r lambda_i phi_i (e_j) = sum_(i = 2)^r lambda_i phi_i (e_j) = 0$, alors $lambda_i = 0 forall i in [|2,r|]$ car $(phi_2, dots, phi_r)$ libre.
]

#proof([Cas où aucun terme carré (on travaille avec les termes rectangles)])[

  Si $f$ ne contient  aucun terme carré, donnons-nous une forme rectangle, par exemple $a x_1 x_2, a in RR^*$
  $
    f(x,x) = a x_1 x_2 + x_1 L(x_3, dots, x_n) + x_2 L_2 (x_3, dots, x_n) + f_2(x_3,dots,x_n)
  $
  où $L_1,L_2$ sont des formes linéaires en $x_3,dots,x_n$ et $f_2$ un polynôme homogène en $x_3, dots, x_n$.
  $
    f(x,x) &= a[x_1x_2 + X_1 L_1(x_3, dots, x_n)/a + x_2 L_2 (x_3, dots, x_n)/a] + f_2 (x_3, dots, x_n \
    &= a[(x_1 + (L_2(x_3, dots, x_n))/a)(x_2 + (L_1(x_3,dots,x_n))/a) - (L_1 (x_3,dots,x_n)L_2(x_3,dots,x_n))/a^2] + f_2 (x_3,dots,x_n) \
    &=^((B)) a[1/4 (x_1 + x_2 + (L_1(x_3,dots,x_n))/a + (L_2(x_3,dots,x_n))/a)^2 - 1/4 (x_1-x_2+ ((L_2(x_3,dots,x_n)-L_1(x_3,dots,_n))/a)^2 )] \
    &- (L_1(x_3,dots,x_n)L_2(x_3,dots,x_n))/a + f_2 (x_3,dots,x_n)
  $

  $q(x_3,dots,x_n) = - (L_1(x_3,dots,x_n)L_2(x_3,dots,x_n))/a + f_2 (x_3,dots,x_n)$ est un polynôme homogène de degré $2$ sur $Vect(e_3, dots, e_n)$.

  Si $q = 0$, c'est fini, si $q != 0$, on applique l'hypothèse de récurrence à $q$ sur $Vect(e_3, dots, e_n)$.

  $q(x_3,dots,x_n) = sum_( i = 3)^s a_i l_i (x_3,dots,x_n)^2$ avec $(l_3,dots,l_s)$ libre dans $Vect(e_3, dots, e_n)^*$

  Posons $ phi_1(x_1,dots,x_n) = x_1 + x_2 + (L_1(x_3,dots,x_n) + L_2(x_3,dots,x_n))/a \
  phi_2(x_1,dots,x_n) = x_1 + x_2 + (L_2(x_3,dots,x_n) - L_1(x_3,dots,x_n))/a \
  forall i = 3,dots,s,phi_i(x_1,dots,x_n) = l_i (x_3,dots,x_n) $

  Il reste à montrer que $phi_1,dots,phi_s$ est libre dans $E^*$

  Soit l'équation $sum_(i = 1)^n phi_i = 0$

  En particulier
  $
    sum_(i = 1)^s lambda_i phi_i (e_i) lambda_1 phi_1(e_i) + lambda_2 phi_2(e_1) = lambda_1 + lambda_2 = 0 \
    sum_(i = 1)^s lambda_i phi_i (e_2) = lambda_1 phi_1(e_2) + lambda_2 phi_2 (e_2) = lambda_1 - lambda_2 = 0
  $
  d'où $cases(lambda_1 + lambda_2 = 0, lambda_1 - lambda_2 = 0) => lambda_1 = lambda_2 = 0$

  On termine comme dans le premier cas pour déduire les autres coefficients.
]

#remark[
  L'algorithme de réduction de Gauss n'est pas unique mais il permet d'obtenir une famille libre sur $E^*$.
]

#theorem[
  Soit $f$ une forme bilinéaire symétrique sur un $RR$-ev de dimension finie $n$. Alors :

  $f$ est définie positive (i.e. produit scalaire) sur $E$ si, et seulement si la réduction de Gauss de $f$ est une combinaison linéaire de $n$ carrés de formes linéaires (indépendantes) à coefficients strictement positifs.
]<critere_def_pos_gauss>

#proof[
  Notons qu'il est nécessaire d'avoir un terme carré à chaque étape de la réduction pour que $f$ soit positive. Si la réduction de Gauss donne une combinaison linéaire de $n$ carrés à coefficients strictement positifs, $f$ sera positive et $f(x,x) = 0$ donne un système homogène de $n$ équations à $n$ inconnues qui est échelonné (puisqu'on enlève une variable à chaque étape). Ce système admet une unique solution qui va être nulle. Donc $f$ est définie.

  Réciproquement :
  Si la réduction de Gauss contient strictement moins de $n$ carrés, le système donné par $f(x,x) = 0$ admettra des solutions non-nulles car il y a moins d'équations indépendantes que d'inconnues. (rq : $f in Lin(RR^n, RR^p), p < n$ n'est jamais injective)
]

#pagebreak()

== Représentation matricielle d'une forme bilinéaire

Soit $E$ un $RR$-ev de dimension $n$, $B in BBB(E)$, $(e_1,dots,e_n)$ une base de $E$.

Prenons $x = sum_(i = 1)^n x_i e_i$, $y = sum_(j = 1^n)y_j e_j$

Par bilinearité, $B(x,y) = sum_(i,j=1)^n x_i y_j B(e_i,e_j)$
Si on pose $a_(i j) = B(e_i,e_j)$, $A = (a_(i j))_(1<=i,j<=n) in M_n (RR)$ est appelée matrice de la forme bilinéaire $B$ dans la base $(e_1,dots,e_n)$.

Maintenant si $X = vec(x_1, vdots, x_n)$, $Y = vec(y_1, vdots, y_n)$, alors :
$
  B(x,y) = transp(X)A Y
$

#example[
  $B(x,y) = 5x_1y_1 - 2x_2y_2 + 4x_3y_3 + 7x_1y_2 + 6x_1y_3 + 6x_3y_1 + 7x_2y_1$

  dans $RR^3, quad x = (x_1,x_2,x_3), y = (y_1,y_2,y_3)$.

  Dans la base canonique de $RR^3$, la matrice de $B$ est :
  $
    A = mat(
      5, 7, 6;
      7, -2, 0;
      6, 0, 4
    )
  $
]

#remark[
  Si $B$ est symétrique, $A$ est symétrique : $forall i,j in [|1,n|] : a_(i j) = B(e_i,e_j) = B(e_j,e_i) = a_(j i)$
]

#theorem("Changement de base")[
  Si $EEE,EEE'$ sont deux bases de $E$, notons $P$ la matrice de passage de $EEE$ à $EEE'$, $A$ la matrice d'une forme bilinéaire $B in BBB(E)$ dans la base $EEE$.

  Alors la matrice de $B$ dans la base $EEE'$ est $transp(P)A P$
]

#remark[
  Attention, il ne faut pas confondre avec le changement de base d'un endomorphisme ($P^(-1) A P$).

  En particulier, $det(transp(P)A P) = det(P)^2 det(A)$ donc on ne peut pas parler de "déterminant d'une application bilinéaire".
]

#proof[
  Notons $A'$ la matrice de $B$ dans la base $EEE' = (f_1,dots,f_n)$ et $EEE = (e_1,dots,e_n)$, si $x = sum_(i = 1)^n x_i e_i = sum_(i = 1)^n x^'_i f_i$ et $y = sum_(j = 1)^n y_j e_j = sum_(j = 1)^n y^'_j f_j$
  $
    X = vec(x_1, vdots, x_n) quad X^' = vec(x^'_1, vdots, x^'_n) quad Y = vec(y_1, vdots, y_n) quad Y^' = vec(y^'_1, vdots, y^'_n)
  $

  On a $X = P X^'$ et $Y = P Y^'$
  $
    forall X,Y in M_n (RR) \
    B(x,y) = transp(X)A Y = transp(P X')A transp(P Y') = transp(X')transp(P)A P Y' = transp(X') A' Y'\
    "Donc "A' = transp(P)A P
  $

  Cette dernière égalité a lieu car l'égalité est vraie pour tout $(x,y) in E^2$. En effet :

  Si : $forall X in RR^n, thick M X = 0$ alors $M = 0$

  $
    (forall X,Y in RR^n, transp(x) M)Y = 0 <==> transp(X) M = 0 <==> transp(transp(X)M) = X transp(M) = 0 \
    <==> transp(M) = 0 = M \
    M = transp(P)A P - A^'
  $
]

#pagebreak()

= Orthogonalité
Soit $(E,scal2(., .))$ un espace euclidien.

#definition[
  Soit $A subset E$ quelconque, on pose :
  $A^ortho = {x in E | scal2(x, y) = 0 forall y in A}$

  $A^ortho$ est un sous-espace vectoriel de $E$ (même si $A$ ne l'est pas) appelé "orthogonal de $A$"
]

#proof[
  Soient $x,x' in A^ortho, lambda in RR$. ALors pour tout $y in A$ :
  $scal2(lambda x + x', y) = lambda scal2(x, y) + scal2(x', y) = 0$

  D'où $lambda x + x' in A^ortho$
]

#proposition[
  Pour tout #underline([sous-espace vectoriel $F$]) de $E$, on a :
  + $dim F + dim F^ortho = dim E$
  + $E = F operp2 F^ortho$
  + $(F^ortho)^ortho = F$
]

#proof[
  On se donne $(v_1,dots,v_p)$ une base de $F$, on la complète en une base $(v_1,dots,v_n)$ de $E$. Si On note $A = (a_(i j))_(1<=i,j<=n)$ la matrice de $scal2(., .)$ dans cette base.

  Si $x = sum_(i = 1)^n x_i v_i, y = sum_(j = 1)^n y_j v_j$. Alors : $scal2(x, y) = sum_(i,j=1)^n a_(i,j) x_i y_j$

  $x in F^ortho <==>^"exo" forall j in [|1,p|] , underbrace(scal2(x, v_j), =transp(X)A V_j) = 0$

  $
    cases(scal2(v_1, x) = 0, vdots, scal2(v_p, x) = 0) <==> cases(sum_(j = 1)a_(1 j) x_j = 0, vdots, sum_(j=1)^n a_(p j) x_j = 0) <==> cases(a_(1 1)x_1 + dots + a_(1 n) x_n = 0, vdots, a_(p 1) x_1 + dots + a_(p n) x+n = 0)
  $

  Ainsi $x in F^ortho$ ssi ses coordonnées $(x_1,dots,x_n)$ sont solutions de ce système à $p$ équations, $n$ inconnues.

  Ces équations sont linéairement indépendantes, car $det(A) != 0$ (on a un produit scalaire). En effet, si $A X = 0, transp(X)A X = scal2(X, X) = 0 ==>^(scal2(., .) "défini") X = 0$

  Le rang du système est $p$ donc l'ensemble des solutions est  l'intersection de $p$ hyperplans linéairement indépendants et est donc de dimension $n-p$. Donc $dim(F^ortho) = n-p$ d'où la première partie.

  Pour la 2nde, Il suffit de montrer que $F inter F^ortho = {0_E}$. Soit $x in F inter F^ortho$, $scal2(x, x) = 0$. Par définition de $scal2(., .)$, $x = 0$.

  Pour la 3e, on a $F subset (F^ortho)^ortho$ car si $x in F$, alors $scal2(x, y) = 0 forall y in F^ortho$. Alors $x in (F^ortho)^ortho$
  et on a :
  $
    dim((F^ortho)^ortho) = dim(E) - dim(F^ortho) = dim(E) - dim(E) + dim(F) = dim(F)
  $
  d'où l'égalité.
]

#example[
  Soit $SSS$ (resp $AAA$) le sev de $M_n (RR)$ formé des matrices symétriques (resp. antisymétriques). On sait que $M_n (RR)$ formé des matrices symétriques (resp. antisymétriques).

  On sait que $M_n (RR) = SSS osum AAA$ ($M = 1/2 underbrace((transp(M) - M), in SSS) + 1/2 underbrace((M - transp(P)), in AAA)$). De plus, $AAA = SSS^ortho$ pour le produit scalaire standard de $MM_n (RR)$ :
  $
    scal2(M, N) = Tr(transp(M)M)
  $
  Prenons $M in SSS, N in AAA$ :
  $
    scal2(M, N) = Tr(transp(M)N) = Tr(M N) = Tr(N M)= Tr(-transp(N) M) = - Tr(transp(N)M) = - scal2(M, N)
  $
  Donc $scal2(M, N) = 0$.
]

#property[
  Soient $F,G$ deux sous-espaces vectoriels d'un espace euclidien $E$.
  + $F subset G ==> F^ortho supset G^ortho$
  + $(F + G)^ortho = F^ortho inter G^ortho$
  + $(F inter G)^ortho = F^ortho + G^ortho$
]

#proof[
  + Soit $y in G, scal2(y, x) = 0 forall x in G supset F$, donc $scal2(y, x) forall x in F, y in F^ortho$.
  + $F subset F + G$ donc $(F + G)^ortho subset F^ortho$ et $G subset F + G$ donc $(F + G)^ortho subset G^ortho$

    Soit : $(F + G)^ortho subset F^ortho inter G^ortho$

    Pour l'inclusion inverse : soient $x in F^ortho inter G^ortho$, $y + z in F + G$.
    $
      scal2(x, y+z) = underbrace(scal2(x, y), x in F^ortho) + underbrace(scal2(x, z), x in G^ortho) = 0
    $
    donc $x in (F+G)^ortho$
  + On applique la 2nde à $F^ortho$ et $G^ortho$. $(F^ortho + G^ortho)^ortho = F^(perp perp) inter G^(perp perp) = F inter G$ et $(F inter G)^ortho = (F^ortho + G^ortho)^(perp perp)$
]

#theorem("De Pythagore")[
  Soit $E$ un espace espace préhilbertien réel.

  Les vecteurs $x,y$ de $E$ sont orthogonaux si, et seulement si, $norm(x + y)^2 = norm(x)^2 + norm(y)^2$
]

#proof[
  $norm(x + y)^2 = norm(x)^2 + norm(y)^2 + 2 scal2(x, y) <==> norm(x + y)^2 = norm(x)^2 + norm(y)^2$
]

#pagebreak()

== Bases orthonormales


#definition[
  Une base $(e_1,dots,e_n)$ d'un espace euclidien $E$ est dite orthogonale si :
  $
    forall i,j in [|1,n|] quad i != j => scal2(e_i, e_j) = 0
  $
  On dit, de plus, qu'elle est orthonormale si :
  $
    forall i,j in [|1,n|] quad scal2(e_i, e_j) = delta_(i,j)
  $
]

#remark("Orale")[
  Dans le cours, on utilisera beaucoup les bases orthonormales, mais le processus d'orthonormalisation étant long, les exercices de TD n'appliqueront généralement que des bases orthogonales.
]

#remark[
  + La matrice d'un produit scalaire dans une base orthogonale est diagonale, et est $I_n$ dans une base orthonormale.
  + Si $(e_1,dots,e_n)$ est une base orthogonale de $E$, alors $(e_1/norm(e_1),dots,e_n/norm(e_n))$ est une base orthonormale de $E$.
  + Toute famille orthogonale formée de vecteurs non-nuls est libre.
] <rq3>

#proof("De la 3e")[
  Soit $(v_1,dots,v_p)$ orthogonale de vecteurs non-nulles.
  Considérons l'équation $sum_(i = 1)^p lambda_i v_i = 0$.

  Alors $forall j in [|1,p|] : scal2(sum_(i = 1)^p lambda_i v_i, v_j) = sum_(i = 1)^p lambda_i scal2(v_i, v_j) = lambda_j scal2(v_j, v_j) = lambda_j norm(v_j)^2 => lambda_j = 0$

  d'où la liberté.
]

#v(3em)

#example[
  La base canonique de $RR^n$ est orthogonale pour le produit scalaire standard.
]

#example[
  Considérons $E = C^0([0,2 pi],RR)$. On munit $E$ du produit scalaire $scal2(f, g) = 1/pi integral_0^(2pi) f(t)g(t)d t$.

  Notons $f_k : x |-> sin(k x)$ pour $k in NN^*$

  La famille $(f_k)_(k in NN^*)$ est orthonormale :

  $
    scal2(f_k, f_l) = 1/pi integral_0^(2 pi) sin(k t)sin (l t) d t = 1/(2 pi) integral_0^(2 pi) cos((k-l) t) - cos((k+l)t)d t
  $

  Si $k != l$, $scal2(f_k, f_l) = 0$.
  Si $k = l$ :
  $
    scal2(f_k, f_k) = norm(f_k)^2 = 1/pi integral_0^(2pi)sin^2(k t) d t = 1/(2pi) integral_0^(2pi) 1-cos(2k t) d t = 1
  $

]

#example[
  conséquences du premier exemple :
  La base canonique $(E_(i j))_(1<=i,j<=n)$ de $M_n (RR)$ (formée par les matrices élémentaires) est orthogonale pour le produit scalaire standard $scal2(M, N) = Tr(transp(M)N)$.

  On rappelle que $E_(i j) = (delta_(i r) delta_(j s))_(1<=r,s<=n)$.
  $
    scal2(E_(i j), E_(k l)) = Tr(E_(j i) E_(k l)) = delta_(i k) delta_(k l)
  $

  Donc non-nul et vaut 1 ssi $(i,j) = (k,l)$ càd $(E_(i j))$ orthonormale.
]

#theorem[
  Un espace euclidien admet toujours une base orthonormale.
]

#proof[
  Il suffit de construire une base orthogonale (cf @rq3). Montrons que tout espace euclidien non-trivial $E$ admet une base orthogonale par récurrence sur $dim(E) = n$.

  + $n = 1$, rien à dire.

  + Supposons le théorème vérifié pour tout ev de dimension $n-1$.

    Soient $E$ de dimension $n$ et $v != 0 in E$, ainsi $dim(Vect(v))^ortho = n-1$

    Par hypothèse de récurrence, $Vect(v)^ortho$ admet une base $(EEE_1,dots,EEE_(n-1))$ orthogonale, $v != Vect(v)^ortho$, donc $(EEE_1,dots,EEE_(n-1),v)$ est une base orthogonale de $E$.


  D'après le théorème de récurrence, la propriété est vérifiée pour tout ev de dimension $n >= 1$
]

=== Procédé d'orthonormalisation

#theorem("Procédé d'orthonormalisation de Gram-Schmidt")[
  Soit $(f_i)_(1<=i<=d)$ une famille libre d'un espace euclidien $(E,scal2(., .))$

  Posons $e_1 = f_1$ et pour tout $k = 1,...,d-1$, $e_(k+1) = f_(k+1) - sum_(i=1)^k scal2(e_i, f_(k+1))/norm(e_i)^2 e_i$

  La famille $(e_i)_(1<=i<=d)$ est orthogonale et pour $k = 1,...,d$, $Vect(e_1, dots, e_k) = Vect(f_1, dots, f_k)$
]

#proof[
  Par récurrence sur $d$ :
  + $d = 1$ : Rien à faire
  + Supposons la construction des $e_1,dots,e_k$ effectuée

    Comme $Vect(e_1, dots, e_k) = Vect(f_1, dots, f_k)$, on a $norm(e_i)^2 = scal2(e_i, e_i) != 0$ pour $i = 1,dots,k$
    et $e_(k+1)$ est bien défini.

    Pour $j = 1,dots,k$ :
    $
      scal2(e_i, e_(k+1)) &= scal2(e_i, f_(k+1)-sum_(j=1)^n scal2(e_j, f_(k+1))/norm(e_j)^2 e_j) = scal2(e_i, f_(k+1)) - sum_(j=1)^k scal2(e_j, f_(k+1))/norm(e_j)^2 scal2(e_i, e_j)\
      &= scal2(e_i, f_(k+1)) - scal2(e_i, f_(k+1))/norm(e_i)^2scal2(e_i, e_i) = 0
    $
    $(e_1,dots,e_(k+1))$ est une famille orthogonale.
    $e_(k+1)in Vect(f_(k+1), e_1, dots, e_k) = Vect(f_(k+1), f_i, dots, f_k)$

    Ainsi $Vect(e_1, dots, e_(k+1)) subset Vect(f_1, dots, f_(k+1))$ et donc l'égalité.
]

#example[
  dans $RR^4$ :
  $v_1 = (1,1,0,0) quad v_2 = (1,0,-1,1),v_3 = (0,1,1,1)$

  $Delta_(1,1) = matdet(1, 0, 0; 0, -1, 1; 1, 1, 1) = -2 != 0$ d'où la liberté

  Posons $e_1 = v_1$ et $norm(v_1) = sqrt(2)$

  $
    e_2 & = v_2 - scal2(v_2, e_1)/norm(e_1)^2 e_1 quad scal2(v_2, e_1) = 1 \
        & = v_2 - 1/2 e_1 = (1,0,-1,1) - 1/2 (1,1,0,0) \
        & = (1/2,-1/2,-1,1)
  $

  #underline([Remarques :])
  + On peut prendre $e_2 = (1,-1,-2,2) = 2 e_2$.
    Si $scal2(u, e_2) = 0$, alors $forall lambda in RR, scal2(u, lambda e_2) = 0$
  + On pose $e_2 = v_2 + lambda e_1$ et on écrit $scal2(e_2, e_1) = 0$. On a :

    $scal2(e_2, e_1) = scal2(e_1, v_2) + lambda scal2(e_1, e_1) = 0$ donc $lambda = - scal2(e_1, v_2)/norm(e_1)^2$

  On pose $e_3 = v_3 - scal2(v_3, e_1)/norm(e_1)^2 e_1 - scal2(v_3, e^'_2)/norm(e_2)^2 e^'_2$

  $scal2(v_3, e_1) = 1, quad norm(e^'_2)^2 = 10, quad scal2(v_3, e^'_2) = -1$

  Donc :
  $
    e_3 = (0,1,1,1) - 1/2 (1,1,0,0) + 1/10 (1,-1,-2,2) = 1/10 (-4,4,8,12) = 1/5 (-2,2,4,6) \
    "(On peut prendre" e^'_3 = (-1,1,2,3) " mais ça ne sera pas orthonormal)"
  $
  Posons $ epsilon_1 = e_1 / norm(e_1) = 1/sqrt(2) (1,1,0,0) \ epsilon_2 = e^'_2/norm(e^'_2) = 1/sqrt(10)(1,-1,-2,2) \ epsilon_3 = e^'_3/norm(e^'_3) = 1/sqrt(15)(-1,1,2,3) $ alors $(epsilon_1,epsilon_2,epsilon_3)$ est une famille orthonormale.

  #underline("Remarque"): On peut poser $e_3 = v_3 + lambda e_1 + mu e^'_2$ et on écrit $cases(scal2(e_3, e_1) = 0, scal2(e_3, e^'_2) = 0)$ qu'on peut résoudre pour retrouver la formule (qu'il faut apprendre, de toute façon.)
]

#remark[
  Ce procédé redémontre le fait que tout espace euclidien possède des bases orthonormées.
]

== Projections et symétries orthogonales

#theorem[
  Soient $(E,scal2(., .))$ un espace euclidien, $x in E$, $F$ un sev de $E$. Il existe un unique vecteur de $F$ noté $p_F (x)$ tel que $x - p_F (x) in F^ortho$. On a de plus :
  + Dans une base $(e_1,dots,e_p)$ *orthonormale* de $F$ :
    $
      p_F (x) = sum_(i=1)^p scal2(x, e_i)e_i
    $
  + L'application $p_F : application(E, F, x, p_F (x))$ est linéaire
  + $norm(x-p_F (x)) = min { norm(x-z), z in F}$
]

#definition[
  - Le vecteur $p_F (x)$ est appelé *projeté orthogonal* de $x$ sur $F$
  - L'application linéaire $p_F$ est la *projection orthogonale* sur $F$
  - On appelle *distance* de $x$ à $F$ le scalaire $norm(x-p_F (x))$ noté $d(x,F)$
]

#remark[
  +$E = F oortho F^ortho$

  $x = p_F (x) + (x-p_F (x))$

  Le théorème de Pythagore donne $norm(x)^2 = norm(p_F (x))^2 + norm(x-p_F (x))^2$

  d'où $d(x,F)^2 = norm(x)^2 - norm(p_F (x))^2$

  + Si $(f_1,dots,f_p)$ est une base orthogonale de $F$ :
    $ p_F = sum_(i=1)^p scal2(x, f_i)/norm(f_i)^2 f_i $

    Dans le procédé d'orthogonalisation de Schmidt, $(f_1,dots,f_p)$ est libre,

    $
          e_1 & = f_i \
          e_2 & = f_2 - p_(Vect(e_1)) in Vect(e_1)^ortho \
        vdots \
      e_(k+1) & = f_(k+1) - p_(Vect(e_1, dots, e_k)) (f_(k+1))
    $
    C'est-à-dire que le procédé n'est qu'une projection échelonnée.
]

#proof("du théorème")[
  + Soit $y = sum_(i=1)^p y_i e_i in F$

    Écrire que $x-y in F^perp$ est équivalent à écrire $scal2(x-y, e_i) = 0, forall i in [|1,p|]$

    ou encore $scal2(x, e_i) = scal2(y, e_i), forall i in [|1,p|]$
    $
      scal2(y, e_i) = scal2(sum_(j=1)^p y_j e_j, e_i) = sum_(j=1)^p y_j scal2(e_j, e_i)
    $
    $(e_1,dots,e_p)$ est orthonormale, $scal2(y, e_i) = y_i scal2(e_i, e_i) = y_i$

    Donc $y = sum_(i=1)^p scal2(x, e_i)e_i$ d'où l'unicité et l'existence de $p_F (x)$ et la première formule.
  + La linéarité de $p_F$ découle de la bilinéarité du produit scalaire dans la formule
  + Soit $z in F$. $ norm(x-z)^2 = norm(x-p_F (x) + (p_F (x) - z))^2 = norm(x-p_F (x))^2 + norm(p_F (x) - z)^2 >= norm(x-p_F (x))^2 $ par le théorème de Pythagore.

    avec égalité ssi $z = p_F (x)$
]

#property[
  Avec les mêmes notations :
  + $p_F compose p_F = p_F$, $Im(p_F) = F$, $Ker(p_F) = F^perp$
  + $p_F + p_(F^ortho) = Id_E$, $p_F compose p_(F^ortho) = p_(F^ortho) compose p_F = 0_(Lin(E))$
  + $forall x in E, norm(p_F (x)) <= norm(x)$
]

#proof[
  + $(p_F compose p_F)(x) = sum_(i = 1)^p scal2(p_F (x), e_i)e_i$ où $(e_1,dots,e_p)$ est une base orthonormale de $F$.

    Or $scal2(p_F (x), e_i) = scal2(sum_(j=1)^p scal2(x, e_j)e_j, e_i) = sum_(j=1)^p scal2(x, e_j) underbrace(scal2(e_j, e_i), delta_(i j)) = scal2(x, e_i)$

    Donc $(p_F compose p_F)(x) = sum_(i=1)^p scal2(x, e_i)e_i = p_F (x)$

    Si $x in Ker p_F$, càd $p_F (x) = 0_E$ alors $x - p_F (x) = x in F^perp$. La réciproque est triviale : $Ker p_F = F^perp$

    Enfin si $x in F, x = p_F (x)$.
    $x = sum_(i=1)^p x_i e_i = sum_(i=1)^p scal2(x, e_i)e_i$

    $scal2(x, e_j) = x_j thick forall j in [|1,p|]$. Donc $Im p_F = F$
  + $E = F operp2 F^perp = F^perp operp (F^perp)^perp$

    $x = p_F (x) + (x-p_F (x)) = p_(F^perp)(x) + underbrace((x - p_(F^perp)(x)), in (F^perp)^perp = F)$

    Donc $x - p_(F^perp)(x) = p_F (x)$ et $x - p_F (x) = p_(F^perp) (x)$ et $p_F + p_(F^perp) = Id_E$

    $p_F (x-p_(F^perp)(x)) = p_F (x) - (p_F compose p_(F^perp))(x)$

    Mais $x - p_(F^perp)(x) = p_F (x)$ car on vient de voir que $p_F + p_(F^perp) = Id_E$.

    $p_F (x-p_(F^perp)(x)) = p_(F)(p_(F)(x)) = p_(F)(x)$ d'où $p_F compose p_(F^perp) = 0$

    De même pour $p_(F^perp) compose p_F$
  + Si $x in E$, $scal2(x-p_(F)(x), p_(F)(x)) = 0$

    Donc $scal2(x, p_(F)(x)) = scal2(p_F (x), p_F (x)) = norm(p_F (x))^2$

    Ainsi $ 0 <= norm(x-p_F (x))^2 = scal2(x-p_(F)(x), x-p_(F)(x)) =^pi norm(x)^2 - norm(p_F (x))^2 \
    <==> norm(x)^2 >= norm(p_F (x))^2 $
]

#definition[
  Soit $F$ un sev d'un espace euclidien $(E,scal2(., .))$.

  On appelle *symétrie orthogonale* par rapport à $F$ l'application linéaire :
  $s_F = p_F - p_(F^perp) = 2 p_F - Id_E = Id_E - 2 p_(F^perp)$
]

#property[
  + $x in F <==> s_F (x) = x quad x in F^perp <==> s_F (x) = -x$
  + $s_F compose s_F = Id_E$
  + $s_F + s_(F^perp) = 0, s_F compose s_(F^perp) = s_(F^perp) compose s_F = -Id_E$
]
#proof[
  Découlent des pptés de $p_F$
]

#example[
  $F = R v = Vect(v)$, $v != 0 in RR^n$

  $p_F (x) = scal2(x, v)/norm(v)^2 v$

  $p_(F^perp)(x) = x - scal2(x, v)/norm(v)^2 v$

  $s_F (x) = 2 p_F (x) - Id_E(x) = 2scal2(x, v)/norm(v)^2v-x$
]

#remark[
  Lorsque $F$ est un hyperplan, $p_(F^perp)$ est une droite, c'est facile en utilisant $s_F = Id_E - S_(F^perp)$.
]

= Morphismes adjoints

Soit $(E,scal2(., .))$ un espace euclidien.

Notons $j : application(E, E^*, y, j(y) : application(E, RR, x, scal2(x, y)))$

$j$ est bien définie : $forall y in E, j(y)$ est linéaire car $scal2(., .)$ est bilinéaire.

#theorem("de représentation de Riesz")[
  Soit $(E,scal2(., .))$ un espace euclidien, l'application $j$ ci-dessus est  un isomorphisme.
] <riesz>

_Autrement dit, pour toute forme linéaire $phi in E^*$, il existe un unique $y$ tel que $phi (x) = scal2(x, y)$_

#proof[
  $j$ est linéaire (déjà vu) car le produit scalaire est bilinéaire. Comme $dim(E) = dim(E^*)$, il suffit de montrer que $j$ est injective.

  Soit $y in E$ tel que $j(y) = 0_(Lin(E, RR))$

  $forall x in E, j(y)(x) = scal2(x, y) = 0$

  En particulier pour $x = y$ : $scal2(x, y) = 0$ càd $y = 0$.

  Donc $Ker(j) = {0}$ càd $j$ injective donc bijective.
]

#corollary[
  Si $EEE = (e_1,dots,e_n)$ est une base *orthonormale* d'un espace euclidien $(E,scal2(., .))$

  La base duale de $EEE$ est $EEE^* = (scal2(., e_1),dots,scal2(., e_n))$ et :

  $forall x in E, x = sum_(i = 1)^n scal2(x, e_i)e_i$

  $forall phi in E^*$, $phi = sum_(i=1)^n phi(e_i) scal2(., e_i)$
]

#corollary[
  Si $u : E --> F$ est une application linéaire entre 2 espaces euclidiens,
  il existe une *unique* application linéaire $u^* : F --> E$ telle que :
  $
    forall (x,y) in E times F, quad scal2(u(x), y)_F = scal2(x, u^*(y))_E
  $
  où $scal2(., .)_F$ (resp. $scal2(., .)_E$) désigne le produit scalaire sur $F$ (resp. E)
]
#proof[
  Soit $y in F$, l'application $x in E |--> scal2(u(x), y)_F in RR$ est une forme linéaire, elle appartient à $E^*$, mais par le théorème de représentation de Riesz, il existe un unique vecteur de $E$, notons-le $u^*(y)$, tel que :
  $
    scal2(u(x), y)_F = j(u^*(y))(x) = scal2(x, u^*(y))_E
  $
  Cela donne l'existence et l'unicité de l'application $u^* : F --> E$, il reste à montrer qu'elle est linéaire.

  $forall y,z in F, forall lambda in RR, forall x in E$ :
  $
    scal2(x, u^*(lambda y + z))_E = scal2(u(x), lambda y + z)_F = lambda scal2(u(x), y)_F + scal2(u(x), z)_F = lambda scal2(x, u^*(y))_E + scal2(x, u^*(y))_E
  $
  d'où :
  $
    forall x in E, quad scal2(x, u^*(lambda y + z) - (lambda u^*(y) + u^*(z)))_E = 0
  $

  ainsi $u^*(lambda y + z) - (lambda u^*(y) + u^*(z)) in E^ortho = {0}$ d'où $u^*(lambda y + z) - (lambda u^*(y) + u^*(z)) = 0$
]

#definition[
  L'application définie ci-dessus est appelé (morphisme) *adjoint* de $u$.
]

_Remarque : dans le cours, on prendra généralement $E = F$_

#example[
  Soit l'espace euclidien E = $MMM_n (RR)$ muni de son produit scalaire standard $scal2(M, N) = Tr(transp(M)N)$

  Donnons-nous $A in E, A != 0_E$, considérons l'endomorphisme
  $
    f_A : application(E, E, M, M A)
  $

  $forall M,N in E, quad scal2(f_A (M), N) = scal2(M A, N) = Tr(transp(M A) N) = Tr(transp(A)(transp(M)N)) = Tr(transp(M)(N transp(A))) = scal2(M, N transp(A)) = scal2(M, f_transp(A)(N))$

  Par *unicité* de l'adjoint : $f_A^* = f_(transp(A))$
]

#property("De l'adjoint")[
  Soient $E,F,G$ des espaces euclidiens
  + $Id_E^* = Id_E$ et si $u in Lin(E, F)$, $u^(**) = u$
  + $u |-> u^*$ est un isomorphisme entre $Lin(E, F)$ et $Lin(F, E)$
  + $forall u in Lin(E, F), v in Lin(F, G)$, $(v compose u)^* = u^* compose v^*$.

    Si $u$ est inversible, $u^*$ aussi. Et $(u^*)^(-1) = (u^(-1))^*$
  + Si $u in Lin(E, F)$, $Ker(u^*) = (Im u)^ortho$ et $Im(u^*) = (Ker u)^perp$
  + Si $EEE$ est une base *orthonormale*, $u in Lin(E)$, la matrice de $u^*$ dans $EEE$ est la transposée de la matrice de $u$ dans la base $EEE$.
  + *(En TD)* Si $EEE$ est une base quelconque, pour $U = Mat_EEE (u)$ $exists M in MMM_n (RR), U^* = M^(-1)transp(U) M$ (avec $M = Mat_EEE (scal2(., .))$)
]

#proof[
  + $forall x,y in E, scal2(Id_E (x), y)_E = scal2(x, y)_E = scal2(x, Id_E (y))_E$. Par unicité de l'adjoint, $Id_E^* = Id_E$

    $forall (x,y) in E times F, scal2(y, u(x))_F = scal2(u^*(y), x)_E = scal2(y, u^(**)(x))_F$ donc $u^(**) = u$.

  + $u |-> u^*$ est linéaire. Soient $u,v in Lin(E, F)$.
    $forall (x,y) in E times F, forall lambda in RR$ :
    $
      scal2(x, (lambda u + v)^*(y))_E & = scal2((lambda u + v)(x), y)_F = lambda scal2(u(x), y)_F + scal2(v(x), y)_F \
                                      & = lambda scal2(x, u^*(y))_E + scal2(x, v^*(y))_E \
                                      & = scal2(x, (lambda u^* + v^*)(y))
    $

    donc $(lambda u + v)^* = lambda u^* + v^*$. Et c'est un isomorphisme puisque $u^(**) = u$
  + $x in E, z in G$ :
    $
      scal2((v compose u)(x), z)_G = scal2(v(u(x)), z)_G = scal2(u(x), v^*(z))_F = scal2(x, u^*(z))_E = scal2(x, (u^* compose v^*)(z))
    $

    On a : $u compose u^(-1) = Id_F$ donc $(u compose u^(-1))^* = (u^(-1))^* compose u^* = Id_F^* = Id_F$

    soit $(u^(-1))^* compose u^* = Id_F$

    $u^(-1) compose u = Id_E$ donnc $u^* compose (u^(-1))^* = Id_E$

    Ainsi $u$ est inversible et $(u^*)^(-1) = (u^(-1))^*$
  + $Ker u^* subset F, y in Ker(u^*)$ :
    $forall x in E, scal2(u^*(y), x)_E = 0 = scal2(y, u(x))_F$

    $y$ est orthogonal à tous les $u(x)$ quand $x$ varie dans $E$ : $y in (Im u)^perp$ et $Ker(u^*) subset (Im u)^perp$

    Soit $y in Im(u)^perp$, alors $forall x in E, scal2(y, u(x))_F = 0 = scal2(u^*(y), x)$ donc $u^*(y) = 0_E$
    et $y in Ker(u^*)$.

    Pour l'autre égalité, on aplique la première égaliteéà $u^*$.
  + Notons $A = Mat_EEE (u), A^* = Mat_EEE (u^*)$

    $scal2(u(x), y)_E = scal2(x, u^*(y))_E$

    Si $EEE = (e_1,dots,e_n)$, $x = sum_(i = 1)^n x_i e_i, y = sum_(i = 1)^n y_j e_j, X = vec(x_1, vdots, x_n), Y = vec(y_1, vdots, y_n)$

    Matriciellement : $scal2(u(x), y) = transp((A X)) I_n Y$

    ($I_n$ matrive du produit scalaire  dans une base orthonormale)

    $scal2(x, u^*(y))_E = transp(X)A^*Y$ d'où $A^* = transp(A)$

    $⚠️$ si $EEE$ n'est plus orthonormale, notons $M$ la matrice du produit scalaire sur $E$.

    On a : $scal2(u(x), y) = transp((A X)) M Y = transp(X)transp(A)M Y$

    et $scal2(x, u^*(y))_E = transp(X)M A^*Y$ donc $transp(A M) = M A^*$.
    $M$ est inversible et $A^* = M^(-1)transp(A)M$

]


#remark[
  La dernière assertion permet de voir que $u$ et $u^*$ ont même trace, même déterminant, même polynôme caractéristique...

]

#method("Calculer un adjoint")[
  Voici trois méthodes pour calculer l'adjoint d'une application linéaire :
  - Résoudre l'équation $scal2(u(x), y) = scal2(x, u^* (y))$
  - Au lieu de travailler avec $Q$ quelconque, on cherche à trouver $u^*$ sur une base.
  - On utilise $U^* = M^(-1)U M$ avec $U = Mat_BBB (u)$ et $M = (scal2(EEE_i, EEE_j))_(1 <= i,j <= n)$, on peut prendre, si c'est plus simple, une base orthonormée.

]

#proposition[
  Si $F$ est un sous-espace vectoriel d'un espace euclidien $E$ stable par un endomorphisme de $E$ ($u(F) subset F$)

  Alors $F^perp$ est stable par $u^*$ ($u^*(F^perp) subset F^perp$)
]

#proof[
  Soit $x in F^perp$, $y in F$.

  $scal2(x, y) = 0$. On doit montrer $u^*(x) in F^perp$.

  $scal2(u^*(x), y) = scal2(underbrace(x, in F^perp), underbrace(u(y), in F)) = 0$ et $u^*(x) in F^perp$
]

#definition[
  Soit $u$ un endomorphisme d'un espace euclidien $E$. On dit que $u$ est :
  + *auto-adjoint* (ou *symétrique*) si $u^* = u$
  + *orthogonal* (ou *isométrie*) si $u in G L(E)$ (càd $u$ bijectif) et $u^* = u^(-1)$
  + *normal* si $u$ et $u^*$ commutent, c'est-à-dire $u^* compose u = u compose u^*$
]

#remark[
  Si $u$ est auto-adjoint ou orthogonal, $u$ est normal.
]

== Endomorphismes des espaces euclidiens
=== Isométries d'un espace euclidien
On note $O(E)$ l'ensemble des endomorphismes orthogonaux (isométries) d'un espace euclidien $E$. $(O(E),compose)$ est le groupe orthogonal :

Si $u,v,w in O(E)$
+ stabilité par $compose$ : $u compose v in O(E), (u compose v)^* = v^* compose u^* = v^(-1) compose u^(-1) = (u compose v)^(-1)$
+ associativité : $(u compose v) compose w = u compose (v compose w)$
+ élément neutre : $Id_E in O(E), Id_E^* = Id_E = Id_E^(-1)$
+ stabilite par passage à l'inverse : Si $u in O(E), u^(-1) in O(E), (u^(-1))^* = (u^*)^(-1) = (u^(-1))^(-1) = u$

#proposition[
  Soit $u$ un endomorphisme d'un espace euclidien $(E,scal2(., .))$ de dimension $n$. Les assertions suivantes sont équivalentes :
  + $u$ est une isométrie ($u in O(E)$)
  + $forall x in E, norm(u(x)) = norm(x)$
  + $forall x,y in E, scal2(u(x), u(y)) = scal2(x, y)$
  + $u$ transforme toute base orthonormale en une base orthonormale :

    Si $(e_1,dots,e_n)$ est orthonormale alors $(u(e_1),dots,u(e_n))$ aussi
  + Il existe une base orthonormale telle que si $A$ est la matrice de $u$ dans cette base : $ transp(A)A = A transp(A) = I_n $
]
_Rermarque : On utilise plutôt les deux dernières_

#proof[

  $(a) => (b)$ :

  $norm(u(x))^2 = scal2(u(x), u(x)) = scal2(x, (u^* compose u)x) = scal2(x, (u^(-1)compose u) x) = norm(x)^2$

  $(b) => (c)$ :

  on utilise une formule de polarisation :
  $
    4 scal2(u(x), u(y)) & = norm(u(x) + u(y))^2 - norm(u(x) - u(y))^2 \
                        & = norm(u(x + y))^2 - norm(u(x-y))^2 =^((b)) norm(x+y)^2-norm(x-y)^2 \
                        & =^"Polarisation" 4scal2(x, y)
  $

  $(c) => (d)$ :

  $(e_1,dots,e_n)$ base ortonormale de $E$ : $scal2(e_i, e_j) = delta_(i,j), quad forall i,j in [|1,n|]^2$

  d'aprês $(c)$ : $scal2(u(e_i), u(e_j)) = delta_(i,j)$
  càd $(u(e_1),dots,u(e_n))$ est orthonormale.

  $(d) => (e)$ :
  $A = (a_(i j))$ la matrice de $u$ dans une base orthonormale $(e_1,dots,e_n)$. D'après $(d)$ : $(u(e_1),dots,u(e_n))$ est orthonormale.

  $delta_(i j) = scal2(u(e_i), u(e_j)) = transp(A e_i)(A e_j)$ (avec $e_i$ vecteur colonne qui vaut $(delta_(i j))_(1 <= j <= n)$)

  $delta_(i j) = transp(e_i)transp(A)A e_j$

  $scal2(e_i, e_j)=transp(e_i) e_j$ d'où $transp(A)A = I_n$

  $(e) => (a)$ :
  $A^(-1) = transp(A)$ donc $A$ est inversible, donc $u$ aussi.

  Dans la base orthonormale donnée par $(e)$, $underbrace(transp(A), "matrice de "u^*) = underbrace(A^(-1), "matrice de "u^(-1))$. Et donc $u^* = u^(-1)$
]

#proposition[
  Si $u in O(E)$, alors $det(u) = +- 1$

  $⚠️$ la réciproque est fausse.
]
#example[
  $A = mat(2, 5; 1, 3)$
  $det(A) = 1$
  $A transp(A) != I_n$ (la base canonique de $RR^2$) est orthonormale pour le produit scalaire standard.
]

#proof[
  $det(u compose u^*) = det(u)det(u^*) <==> det(I_n) = det(u)^2$
  d'où $det(u) = +-1$
]

#definition[
  Le groupe spécial orthogonal (ou groupe des rotations vectorielles de $E$) est le groupe :
  $ S O(E) = {u in O(E) | det(u) = 1} $
]
#proposition[
  Soit $F$ un sous-espace vectoriel d'un espace euclidien $E$.

  La symétrie orthogonale $s_F$ par rapport à $F$ est une isométrie (auto-adjointe également).

]

#proof[
  Une projection orthogonale $p_F$ est auto-adjointe $(p_F^* = p_F)$

  $forall x,y in E, scal2(p_F (x), y) = scal2(p_(F)(x), y-p_(F)(y) + p_(F)(y)) = scal2(p_(F)(x), y-p_F (y)) + scal2(p_F (x), p_F (y)) = scal2(p_F (x), p_F (y))$

  De la même façon:
  $
    scal2(x, p_F (y)) = scal2(x-p_F (x) + p_F(x), p_F(y)) = ... = scal2(p_F (x), p_F (y))
  $

  Donc $forall x,y in E$ : $scal2(p_F (x), y) = scal2(x, p_F (y))$ et $p_F^* = p_F$
  - $s_F$ est autoadjointe : $s_F = 2p_F - Id_E, s_F^* = 2p_F - Id^*_E = 2p_F - Id_E = s_F$
  - $s_F$ est une isométrie : $s_F^* compose s_F = s_F compose s_F = Id_E = s_F compose s_F^*$ donc $s_F^* = s_F^(-1)$
]

#definition[
  Une symétrie orthogonale par rapport à un hyperplan est appelée *réflexion*.

  (Une symétrie orthogonale par rapport à une droite est appelée *demi-tour* ou *retournement*)
]

#remark[
  Si $H$ est un hyperplan, $e$ un vecteur unitaire base de $H^perp$.

  $
    forall x in E, s_H (x) = x - 2p_(H^perp)(x) = x-2scal2(x, e)e
  $
]

#theorem[
  Soit $u$ une isométrie d'un espace euclidien $E$.

  Notons $r = Rg(u-Id_E)$, alors $u$ est la composée d'au plus $r$ réflexions.
]

#remark[
  On dit que les réflexions engendrent le groupe orthogonal $O(E)$
]

#proof[
  Par récurrence sur $r$.
  - Si $r = 0$, $u = Id_E$ est la composée de $0$ réflexions.
  - Supposons le théorème vrai pour tout $0 <= r'< r$ et supposons $u != Id_E$

    Ainsi, il existe $y in E$ tel que $u(y) != y$. Posons $z = u(y) - y$, $F = Vect(z)^perp$ un hyperplan de $E$.

    $norm(z)^2 = norm(u(y)-y)^2 = norm(u(y))^2 + norm(y)^2 - 2 scal2(u(y), y) = 2 norm(y)^2 - 2scal2(u(y), y)$

    Soit $s_F$ la symétrie orthogonale par rapport à $F$ ($s_F$ est une réflexion).

    $
      s_F (x) & = (Id_E - 2 p_(F^perp)) (x) = x - 2 scal2(x, z)/norm(z)^2 z \
      s_F (y) & = y - 2 scal2(y, u(y)-y)/(2 norm(y)^2 - 2 scal2(u(y), y))(u(y)-y) \
              & = y - (scal2(y, u(y)) - norm(y)^2)/(norm(y)^2 - scal2(u(y), y))(u(y) - y) = u(y) \
      s_F (z) & = z - 2 scal2(z, z)/norm(z)^2 z = -z
    $

    Maintenant si $x$ vérifie $u(x) = x$, i.e. $x in Ker(u-Id_E) :$

    $scal2(x, u(y)-y) = scal2(x, u(y))-scal2(x, y) = scal2(u(x), u(y))-scal2(x, y) = 0$ et $s_F (x) = x$

    Considérons $s_F compose u$, si $s_F = Rg(s_F compose - Id_E)$, on a $r^' <= r = Rg(u-Id_E)$ car $Ker(u - Id_E) subset Ker(s_F compose u - Id_E)$ ($u(x) = x ==> (s_F compose u) (x)$) et donc par le théorème du rang on a le résultat.

    De plus : $(s_F compose u)(y) = (s_F compose s_F)(y) =^"symétrie" y$

    Ainsi $y in Ker((s_F compose u) - Id_E) without Ker(u-Id_E)$

    Donc on a $r' < r$

    Par hypothèse de récurrence, $s_F compose u$ est la composée d'au plus $r'$ réflexions :

    $s_F compose u = s_1 compose dots compose s_k$ avec $k <= r^'$ et $s_i$ des réflexions.

    et $u = s_F compose s_1 compose dots compose s_K$ est la composée de $(k+1) <= r$ réflexions.
]

#theorem[
  Soit $u in O(E)$ :
  + $Sp(u) subset {+- 1}$ et, quand cela a un sens, les sous-espaces propres $E_1 = Ker(u-Id_E)$ et $E_(-1) = Ker(u + Id_E)$ sont orthogonaux
  + $u$ est diagonalisable *si, et seulement si* $u$ est une symétrie orthogonale.
  + Soit $F$ un sous-espace vectoriel de $E$. Si $F$ est stable par $u$ alors $F^perp$ aussi et la restruction $restr(u, F)$ de $u$ à $F$ (resp $restr(u, F^perp)$ de $u$ à $F^perp$) est une isométrie de $F$ (resp. $F^perp$)
  + $E = Ker(u - Id_E) operp2 Im(u-Id_E)$
  + Si la dimension de $E$ est impaire et si $u in S O(E)$, alors $1$ est valeur propre de $u$.
]

#proof[
  + Soient $lambda$ une valeur propre de $u$ et $x != 0$ un vecteur propre associé.
    $norm(x) = norm(u(x)) = norm(lambda x) = abs(lambda) norm(x) => abs(lambda) = 1 <==> lambda = +- 1$

    Soient $x in E_1, y in E_(-1), scal2(x, y) = scal2(u(x), u(y)) = scal2(x, -y) = -scal2(x, y) <==> scal2(x, y) = 0$
  + Une symétrie orthogonale est diagonalisable. Réciproquement, si $u in O(E)$ est diagonalisable :
    $
      E = Ker(u - Id_E) operp2 Ker(u + Id_E)
    $
    et $u$ est la symétrie par rapport à $Ker(u-Id_E)$
  + Si $F$ est stable par $u$, $F^perp$ est stable par $u^* = u^(-1)$
    donc $u^(-1)(F^perp) subset F^perp$ et $F^perp subset u(F^perp)$. Comme $u$ est bijective, $F^perp$ et $u(F^perp)$ ont même dimension : $u(F^perp) = F^perp$
  + On sait que $Ker(u-Id_E)^* = Im(u-Id_E)^perp$, or $(u-Id_E)^* = u^* - Id_E = u^(-1)-Id_E = u^(-1) compose (Id_E - u)$ et $Ker(u-Id_E)^* = Ker(u^(-1) compose (Id_E - u)) = Ker(Id_E - u) = Ker(u - Id_E) = Im(u-Id_E)^perp$
  + $u - Id_E = u compose (Id_E - u^(-1)) = u compose (Id_E - u^*) = u compose (Id_E - u)*$

    $det(u-Id_E) = det(u compose (Id_E - u)^*) = det(u) cdot det((Id_E - u)*) = det(u) cdot det(Id_E - u)$.

    On a $det(u) = 1$ car $u in S O (E)$ et $det(Id_E - u) = (-1)^dim(E) det(u - Id_E)$ (car $det(lambda u) = lambda^dim(E) det(U)$ pour tout $lambda in RR$)

    Si $dim(E)$ est impaire, $det(u-Id_E) = 0$ et $1$ est valeur propre.

]

== Orientation
Soit $E$ un espace euclidien de dimension $n$, soient $BBB,BBB^'$ deux bases de $E$, notons $det_BBB (BBB')$ le déterminant de la matrice de passage $P_BBB^(BBB') = Mat_((BBB',BBB)(Id_E))$.

#remark[
  On a $det_(BBB^')(B) = 1/(det_BBB (B))$ donc $det_(BBB^')(BBB)$ de même signe que $det_BBB (BBB^')$.
]

#definition[On définit sur l'ensemble des bases de $E$ la relation :
  $
    BBB tilde BBB' <==> det_BBB (BBB' > 0)
  $]

#property[
  Cette relation est une relation d'équivalence et il y a exactement deux classes d'équivalence.
]

#proof[
  - Réflexivité :
    $det_BBB (BBB) = det(I_n) = 1 > 0 ==> BBB tilde BBB$
  - Symétrie : donnée par la remarque suivante
  - Transitivité :  $BBB,BBB^',BBB^('')$ bases de $E$.
    Suppsoons que $det_BBB (BBB^') > 0$ et $det_(BBB^')(BBB^('')) > 0$

    Or $det_BBB (BBB^('')) = det_(BBB^')(BBB^'') det_BBB (BBB^') > 0$

    Fixons une base $BBB = (e_1,dots,e_n)$ de $E$ et soit $BBB^'$ une autre base de $E$. On a deux cas :

    + $det_(BBB)(BBB^') > 0 => BBB tilde BBB^', BBB'$ est dans la classe de $BBB$
    + $det_BBB (BBB^') < 0, BBB^'$ est dans la classe d'équivalence de $(e_1,dots,e_(n-1),-e_n)$
]

#definition[
  Orienter un espace euclidien $E$ revient à fixer une base $BBB_0$ de $E$.

  On dit alors qu'une base $BBB$ de $E$ est directe si $BBB in Cl_tilde (BBB_0)$, indirecte sinon.
]

#example[
  $E = RR^2$, $BBB_0 = (i,j) = (vec(1, 0),vec(0, 1))$

  - $(j,-i)$ est directe : $matdet(0, -1; 1, 0) = 1$
  #v(.5em)
  - $(i,-j)$ est indirecte : $matdet(1, 0; 0, -1) = -1$
]

#example[
  $E = RR^3$, on utilise la règle du tire-bouchon/tourne-vis/bonhomme d'ampère.
]
#h(1em)
Fixons $BBB_0 = (e_1,dots,e_n)$ une base orthonormale qui oriente $E$.

Soient $x_1,dots,x_n$ des vecteurs de $E$ non-nuls et $BBB$ une base de $E$.

$det_(BBB_0)(x_1,dots,x_n) = det_(B_0)(B) det_BBB (x_1,dots,x_n)$

Si $BBB$ est directe, $det_(BBB_0)(x_1,dots,x_n)$ et $det_BBB (x_1,dots,x_n)$ ont même signe.

Le signe de $det_BBB (x_1,dots,x_n)$ ne dépend pas de la base directe choisie.

Notons $[x_1,dots,x_n] = det_(BBB_0)(x_1,dots,x_n)$

L'application $ application(E, RR, x, [x_1,dots,x_(n-1),x]) $ est une forme linéaire ($phi in E^*$). Par le théorème de représentation de Riesz, il existe un unique vecteur $a$ de $E$ tel que :
$
  [x_1,dots,x_(n-1),x] = scal2(a, x)
$

#definition[
  Le vecteur $a$ ci-dessus est appelé produit vectoriel (ou exterieur) de $x_1,dots,x_(n-1)$ et est noté $ a = x_1 and dots and x_(n-1) $
]

#proposition[
  Avec les mêmes notations, $x_1 and dots and x_(n-1)$ est orthogonal à $x_i$, $i = 1,dots,n-1$
]

#proof[
  Pour $i = 1,dots,n-1$, $scal2(x_1 and dots and x_(n-1), x_i) = [x_1,dots,x_(n-1),x_i] = 0$
]

#remark[
  $abs(scal2(x_1 and dots and x_(n-1), x_n))$ est un volume.
]

#corollary[
  Soit $H$ est un hyperplan de $E$ de base $(x_1,dots,x_(n-1))$.

  Alors $H^perp = Vect(x_1 and dots and x_(n-1))$ et pour tout $x in E$ :

  $p_H (x) = x - scal2(x_1 and dots and x_(n-1), x)/norm(x_1 and dots and x_(n-1))^2 x_1 and dots and x_(n-1)$ et $underbrace(d(x,H), =norm(x-p_H (x))) = abs(det_(BBB_0)(x_1,dots,x_(n-1),x))/norm(x_1 and dots x_(n-1))$
]

#example[
  $E = RR^3$, $BBB_0 = (i,j,k)$ la base canonique.

  $x_1 = (a,b,c), x_2 = (a^',b^',c^'), u = (x,y,z)$

  $scal2(x_1 and x_2, u) = det M$ où $M = mat(a, a^', x; b, b^', y; c, c^', z)$

  Développons par rapport à $C_11$ :
  $det M = x(b c^' - b^' c) - y (a c^' - a^' c) + z (a b^' - a^' b) = scal2(x_1 and x_2, u)$

  D'où $x_1 and x_2 = vec(a, b, c) and vec(a^', b^', c^') = vec(b c^' - b^'c, -(a c^' - a^' c), a b^'-a^' b)$
]

#pagebreak()

== Groupe orthogonal en petite dimension : $O(RR^n)$ ("$O(n)$")

=== En dimension 1
$O(1) = {+- I_1}$, $S O(1) = {I_1}$
=== En dimension 2
On considère $RR^2$ orienté par sa base canonique muni de son produit scalaire standard et soit $u in O(2)$ dont la matrice dans la base canonique (orthonormale pour le p.s. standard) est :
$
  A = mat(a, c; b, d)
$
On a : $a^2 + b^2 = 1 = c^2 + d^2$ et $a c + b d = 0$
Il existe des réels $theta, phi$ tels que $a,b = cos(theta), sin(theta)$ et $c,d = cos(phi), sin(phi)$
$det(A) = a d - b c = cos(theta)sin(phi)-sin(theta)cos(phi) = sin(phi - theta)$
D'autre part $0 = a c + b d = cos(theta)cos(phi) + sin(theta)sin(phi) = cos(phi-theta)$
On a deux cas :
+ $det(A) = 1 <==> u in S O(2)$

  $cases(sin(phi-theta) = 1, cos(phi-theta) = 0) ==> phi - theta = pi/2 + 2 k pi, k in ZZ <==> phi = theta + pi/2 + 2 k pi$

  $
    A = mat(cos(theta), cos(theta + pi/2); sin(theta), sin(theta+pi/2)) = mat(cos(theta), -sin(theta); sin(theta), cos(theta))
  $

  On reconnaît la matrice d'une rotation vectorielle de $theta$.

  #remark[$Tr(A) = 2cos(theta)$]

+ $det(A) = -1$

  $cases(sin(phi-theta) = -1, cos(phi-theta) = 0) ==> phi - theta = -pi/2 + 2 k pi, k in ZZ <==> phi = theta - pi/2 + 2 k pi$

  $ A = mat(cos(theta), sin(theta); sin(theta), -cos(theta)) $ dans ce cas, c'est une réflexion.

  En effet, posons $f_1 = cos(theta/2)e_1 + sin(theta/2)e_2$ et $f_2 = -sin(theta/2)e_1 + cos(theta/2)e_2$

  avec $(e_1,e_2)$ base canonique de $RR^2$.

  #remark[$(f_1,f_2)$ est une base orthonormale directe de $RR^2$]

  Dans cette base, la matrice de $u$ est $mat(1, 0; 0, -1)$ et $u$ est la réflexion par rapport à la droite $Vect(f_1)$

  $A f_1 = mat(cos(theta), sin(theta); sin(theta), -cos(theta))vec(cos(theta/2), sin(theta/2)) = vec(cos(theta)cos(theta/2) + sin(theta)sin(theta/2), sin(theta)cos(theta/2)-cos(theta)sin(theta/2)) = vec(cos(theta/2), sin(theta/2)) = f_1$

  $A f_2 = mat(cos(theta), sin(theta); sin(theta), -cos(theta))vec(-sin(theta/2), cos(theta/2)) = ... vec(sin(theta-theta/2), -cos(theta-theta/2)) = vec(sin(theta/2), -cos(theta/2)) = -f_2$

#remark[
  Une rotation est la composée de deux réflexions.
]
#proof[
  Notons $(e_1,e_2)$ la base canonique de $RR^2$ et $f_1 = cos(theta/2)e_1 + sin(theta/2)e_2$

  soient $s_e$ la réflexion par rapport à $e_1$, $s_f$ la projection par rapport à $f_1$

  Alors $(s_f compose s_e)(e_1) = s_f (e_1) = e_1 - 2 p_(Vect(f_1)^perp)(e_1)$.

  $Vect(f_1)^perp = Vect(f_2)$ avec $f_2 = -sin(theta/2)e_1 + cos(theta/2)e_2$

  $p_(Vect(f_1)^perp)$ est la projection orthogonale sur $Vect(f_2)$

  $
    p_(Vect(f_1)^perp)(e_1) &= scal2(e_1, f_2)f_2, quad scal2(e_1, f_2) = -sin(theta) \
    &= -sin(theta/2)(-sin(theta/2)e_1 + cos(theta/2)e_2) \
    (s_f compose s_2)(e_1) &= e_1 - 2 p_(Vect(f_1)^perp)(e_1) = ... = (1-2sin^2(theta/2))e_1 + 2sin(theta/2)cos(theta/2)e_2\
    &= cos(theta)e_1 + sin(theta)e_2
  $

  $(s_f compose s_e)(e_2) = -s_f (e_2)$ car $s_e (e_2) = -e_2 = -e_2 + 2p_(Vect(f)^perp)(e_2)$

  $
    p_(Vect(f_₁^perp))(e_2) &= scal2(e_2, f_2)f_2 = cos(theta/2)(-sin(theta/2)e_1 + cos(theta/2)e_2) \
    (s_f compose s_e)(e_2) &= -e_2 + 2cos(theta/2)(-sin(theta/2)e_1 + cos(theta/2)e_2) \
    &= -2cos(theta/2)sin(theta/2)e_1 + (2cos^2(theta/2)-1)e_2
    &= -sin(theta)e_1 + cos(theta)e_2
  $
]

=== Dimension 3

$u in O(3), E = RR^3$

Puisque nous sommes en dimension impaire, $u$ admet une valeur propre réelle.

Notons $H = Ker(u - Id_E) = E_1$ le sous-espace propre associé à la valeur 1 et raisonnons sur sa domension

+ $dim H = 3, E_1 = R^3$ et $u = Id_E$
+ $dim H = 2$, $1$ valeur propre de multiplicité $2$ ($u != Id$) et $-1$ de multiplicité $1$
  $u$ est diagonalisable. Dans une base de vecteurs propres, la matrice de $u$ est $mat(1, 0, 0; 0, 1, 0; 0, 0, -1)$ et $u$ est une réflexion par rapport à $H$.

+ $dim H = 1$, considérons la restriction de $u$ à $H^perp$ $restr(u, H^perp)$

  $restr(u, H^perp)$ est une isométrie, mais pas une réflexion (car elle n'a pas de point fixe), c'est donc une rotation.

  Dans une base orthonormale adaptée à la décomposition $RR^3 = H^perp operp2 H$, la matrice de $u$ est $mat(cos(theta), -sin(theta), 0; sin(theta), cos(theta), 0; 0, 0, 1)$. C'est donc une rotation d'angle $theta$ d'axe $H = E_1$
+ $dim(H) = 0$, $-1$ est l'unique valeur propre
  + de multiplicité $3$, donc $u = -Id_E$
  + $-1$ est valeur propre de multiplicité $1$, considérons $restr(u, E_(-1)^perp)$ la restriction de $u$ à $E^perp_(-1) = Ker(u+Id_e)^perp$

    $restr(u, E_(-1)^perp)$ est une rotation (cf le cas d'avant)

    Dans une base adaptée à la décomposition : $RR^3 = E_(-1)^perp operp2 E_(-1)$

    la matrice de $u$ est $mat(cos(theta), -sin(theta), 0; sin(theta), cos(theta), 0; 0, 0, -1)$. $u$ est donc la composée de la rotation d'angle $theta$ et de la réflexion par rapport à $E_(-1)^perp$

*Résumé* : Si $u in O(3)$, il existe une base orthonormale de $RR^3$ dans laquelle la matrice de $u$ est de la forme :
$
  mat(cos(theta), -sin(theta), 0; sin(theta), cos(theta), 0; 0, 0, epsilon) quad "avec" epsilon = +-1, theta in RR
$

#underline[Premier cas] : $epsilon = 1 = det(u)$, $u$ est une rotation d'angle $theta$ d'axe $E_1 = Ker(u-Id_E)$

Notons $(f_1,f_2)$ une base orthonormale directe de $E_1^perp$ (si $dim E_1 = 1$) et $f_3 = f_1 and f_2$. On a :

$Tr(u) = 2cos(theta) + 1 <==> cos(theta) = (Tr(u)-1)/2$

et $sin(theta) = det(f_1, u(f_1), f_3)$. En effet, $u(f_1) = cos(theta)f_1 + sin(theta)f_2, f_1 and u(f_1) = sin(theta)f_3$

Or $scal2(f_1 and u(f_1), f_3) = det(f, u(f_1), f_3) = sin(theta)$

#underline[Second cas] : $epsilon = -1 = det(u)$,
- $u$ est la réflexion par rapport à $E_(-1)^perp$
- est la composée d'une rotation et d'une réflexion par rapport à $E_(-1)^perp$.
  On a encore $Tr(u) = 2cos(theta)-1$ et $sin(theta) = det(f_1, u(f_1), f_3)$ avec les mêmes notations que précédemment.

= Théorème spectral

#remark("Rappel")[
  Un endomorphisme $u in Lin(E)$, avec $E$ euclidien, est *auto-adjoint* (symétrique) si $u^* = u$
]

#remark[
  Dans une base orthonormée, la matrice d'un endomorphisme auto-adjoint est symétrique.
]

#example[
  Une projection orthogonale est auto-adjointe.
]

#proposition[
  Soit $u$ un endomorphisme auto-adjoint de $E$ :
  + Les sous-espaces propres de $u$ sont deux-à-deux orthogonaux
  + Si $F$ est un sous-espace de $E$ stable par $u$ ($u(F) subset F$) alors $F^perp$ l'est aussi.
]

#proof[
  + Soient $lambda != mu$ deux valeurs propres distincte de $u$ et $x,y$ deux vecteurs propres associés.

    $mu scal2(x, y) = scal2(x, mu y) = scal2(u^*(x), y) = scal2(u(x), y) = lambda scal2(x, y)$

    Puisque $mu != lambda$, on a forcément $scal2(x, y) = 0$
  + On sait que $F^perp$ est stable par $u^* = u$
]

#remark("Rappel sur les polynômes annulateurs")[
  Soit $P in RR[X]$, on dit que $P$ est annulateur de $u$ si $P(u) = 0$

  $P(X) = sum_(i = 0)^d a_i X_i$, $P(u) = sum_(i = 0)^d a_i u^i$ avec $u^i = underbrace(u compose u compose ... compose u, i "fois")$ et $u^0 = Id$

  Le polynôme caractéristique est un polynôme annulateur (Cayley-Hamilton)

  Il existe un unique polynôme annulateur *unitaire* (de coefficient dominant 1) qui divise tous les polynômes annulateurs, c'est ce que l'on appelle le *polynôme minimal*.

  Le polynôme minimal admet pour racines toutes les valeurs propres de l'endomorphisme considéré (et uniquement les valeurs propres).

  Un endomorphisme est diagonalisable ssi son polynôme minimal est *scindé* et *à racines simples*.
]

#example[
  - Si $u = Id_E$, $pi_u (X) = X - 1$
  - Si $u = p$ une projection non-nulle et != Id, $p compose p = p$ donc $X^2 - X = X(X-1)$ est annulateur et on peut facilement montrer que $pi_u = X(X-1)$
  - Si $u = s$ une symétrie différente de $-Id, Id, 0$. $s compose s = Id <==> X^2 - 1 = (X-1)(X+1)$ annulateur et facilement, $pi_u = (X-1)(X+1)$
]

#lemma[
  Soit $E$ un $RR$-espace vectoriel de dimension $n >= 1$. Considérons $u$ un endomorphisme non-nul. Il existe dans $E$ une droite ou un plan stable par $u$.
] <lemme_sev_stable>

#proof[
  Si $x in Sp(u)$, alors $Vect(x)$ stable par $u$ ($u(x) = lambda x in Vect(x)$).

  Supposons que $u$ n'ait pas de vecteur propre.

  Le polynôme minimal $pi_u$ de $u$ est un produit de polynômes de degré 2 à discriminants strictement négatifs.

  $pi_u (X) = (X^2 - a X + b)Q(X)$ avec $a^2 -4b < 0$ et $Q$ polynôme non-annulateur de $u$.

  Il existe donc $y in E$ tel que $Q(u)(y) != 0_E$

  Posons $z = Q(u)(y)$ et soit $P = Vect(z, u(z))$. Montrons que $dim P = 2$ et $P$ est stable par $u$.

  - $dim(P) = 2$ : La famille $(z,u(z))$ est libre car $u$ n'a pas de vecteur propre ($z != 0_E, u(z) != 0_E$ et $u(z) = lambda z => z in Sp u$).

  - $P$ stable par $u$ : il faut et suffit de montrer que $u^2 (z) in P$
    $0 = pi_u (u(y)) = (u^2 + a u + b Id) compose (Q(u))(y) = (u^2 + a u + b Id)z$

    donc $u^2 (z) = a u(z) - b z in P$
]

#theorem("Spectral")[
  Soit $u$ un endomorphisme d'un espace euclidien $E$. Les assertions suivantes sont équivalentes :
  + $u$ est auto-adjoint
  + Il existe une base *orthonormale* de $E$ formée des vecteurs propres de $u$ (en particulier, $u$ est diagonalisable)
]
#proof[
  $1) ==> 2)$ :
  Par récurrence sur $n = dim(E)$

  + Cas $n = 1$, rien à montrer..

    Cas $n = 2$, soit $EEE$ une base orthonormale de $E$ dans laquelle $Mat_EEE (u) = mat(a, b; b, d) = A$

    Le polynôme caractéristique $P_A (X) = X^2 - Tr(A)X + det(A) = X^2 - (a + d)X + (a d - b^2)$

    Son discriminant est $delta = (a+d)^2 - 4 (a d - b^2) = (a-d)^2 + 4b^2 >= 0$

    Si $delta = 0$, alors $a = 0$ et $b = 0$, $u$ est une homothétie, c'est fini

    Sinon, $delta > 0$, $u$ admet deux valeurs propres distinctes et est donc diagonalisable, et comme les sous-espaces propres sont orthogonaux,
    on peut facilement trouver une base orthonormale de vecteurs propres.
  + Pour $n > 2$, supposons l'implication démontrée pour tous les espaces de dimension $<= n-1$.
    Soit $E$ de dimension $n$. Par le lemme, $E$ admet une droite ou un plan $F$ stable par $u$.

    La restriction $restr(u, F)$ est auto-adjointe, donc par hypothèse de récurrence, il existe une base orthonormale $EEE$ qui diagonalise $restr(u, F)$. Maintenant, $G = F^perp$ est stable par $u$ et la restriction $restr(u, G)$ est autoadjointe. Par hypothèse de récurrence, il existe une base orthonormale $FFF$ de $G$ qui diagonalise $restr(u, G)$. La concaténaton de $EEE$ et $FFF$ est une base de $E$ qui répond à la question ($E = F operp2 G$).

  On conclut par récurrence.

  $2) ==> 1)$ :
  Évident car une matrice diagonale dans une base *#underline[orthonormale]* est symétrique.
]

#corollary[
  Toute matrice symétrique réelle est diagonalisable.
]

#remark[
  Pour tout matrice symétrique réelle $A in SSS_n (RR)$
  , il existe une matrice orthogonale $P in O(n)$ telle que $transp(P)A P$ soit diagonale.
  En effet, on sait qu'il existe une base orthonormale de $RR^n$ constituée de vecteurs propres.

  (rappel : $P^(-1) = transp(P)$ pour $P$ orthogonale)
]

#remark("⚠️")[
  Les matrices symétriques à coefficients complexes non-réelles ne sont pas forcément diagonalisables.
]

#example[
  Pour $A = mat(0, 1; 1, 2i)$, $P_A (X) = X^2 - 2i X - 1 = (X-i)^2$ $A$ n'est pas diagonalisable.
]

== Réduction des endomorphismes antisymétriques

_$v in Lin(E)$ est antisymétrique si $v^* = -v$_


#lemma[
  si $v$ est un endomorphisme antisymétrique d'un espace euclidien, sa seule valeur propre est $0$.
]

#proof[
  Soit $lambda in Sp v$ et $x$ vecteur propre associé à $lambda$.

  On a : $lambda scal2(x, x) = scal2(lambda x, x) = scal2(v(x), x) = scal2(x, v^*(x)) = scal2(x, -v(x)) = scal2(x, -lambda x) = -lambda scal2(x, x)$

  Et comme $scal2(x, x) = norm(x)^2 != 0$, on a $lambda = 0$.
]

#theorem[
  Soit $v$ un endomorphisme antisymétrique d'un espace euclidien $E$, il existe une base orthonormale de $E$ dans laquelle la matrice de $v$ est de la forme :

  $
    mat(0, , , , , ; , ddots, , 0; , , 0; , , , BBB_1; , , , , ddots; , , , , , BBB_n)
  $

  avec $BBB_i = mat(0, alpha_i; -alpha_i, 0)$ avec $alpha_i in RR^*$
]

#proof[
  Par récurrence sur $dim E = n$

  + Si $n = 1$, rien à dire $v = 0$
  + Si $n = 2$, dans une base orthogonale de $E$, la matrice de $v$ est antisymétrique donc de la forme $mat(0, alpha; -alpha, 0)$, $alpha in RR$
  + Soit $n > 2$ tel que l'on suppose le résultat vrai pour tout espace euclidien de dimension inférieure à $n$.

    On sait qu'il existe un sous-espace $F subset E$ de dimension $1$ ou $2$ stable par $v$ (@lemme_sev_stable).

    - Si $dim F = 1$, $restr(v, F)$ est l'application nulle : $restr(v, F) = 0$
    - Si $dim F = 2$, dans une base orthonormale de $E$, la matrice de la restriction $restr(v, F)$ de $v$ à $F$ est de la forme $mat(0, alpha; -alpha, 0)$ avec $alpha in RR^*$

    $E = F operp2 F^perp$, $F^perp$ est stable par $v^* = -v$ donc stable par $v$

    par hypothèse de récurrence, comme $dim F^perp <= n-1$, il existe une base $BBB$ orthogonale de $F^perp$ dans laquelle la matrice de $restr(v, F^perp)$ est du type donné dans le théorème. En concaténant $BBB$ avec une base orthonormale de $F$, on obtient le résultat
]

== Réduction des endomorphismes orthogonaux
#theorem[
  Soit $u in O(n)$, il existe des entiers positifs $p,q$ et $r$ tels que $p + q + 2 r = n$ et une base orthonormée de $RR^n$ dans laquelle la matrice de $u$ est du type :
  $
    mat(
      I_p, 0, dots, , 0; 0, -I_q, ddots, , vdots; vdots, ddots, R_(theta_1), ddots; , , ddots, ddots, 0; 0, dots, dots, 0, R_(theta_r)
    )
  $
  où : $forall i in [|1,r|]$, $R_(theta_i) = mat(cos(theta_i), -sin(theta_i); sin(theta_i), cos(theta_i))$, $theta_i in RR without pi ZZ$
]

#proof[
  On sait déjà que les sous-espaces propres (s'ils existent) $E_1$, $E_(-1)$ associés aux valeurs propres $1$ et $-1$ sont en somme directe orthogonale $(dim E_1 = p, dim E_(-1) = q)$

  Posons $F_0 = (E_1 osum E_(-1))^perp$
  - Si $F_0 = {0}$, c'est fini, il existe une b.o.o dans laquelle la matrice de $u$ est $mat(I_p, 0; 0, -I_q)$ et $u$ est une symétrie orthogonale (par rapport à $E_1$)
  - Sinon, comme $E_1 operp2 E_(-1)$ est stable par $u$, $F_0$ aussi.

    La restriction $restr(u, F_0)$ n'admet pas de valeur propre.

    Posons $v_0 = restr(u, F_0) + restr(u^*, F_0)$, on a $v^*_0 = v_0$ et $v_0$ est auto-adjoint donc diagonalisable dans une base orthonormale par le théorème spéctral.

    Soit $omega in F_0$ un vecteur propre dwe $V_0$ associé à une valeur propre $lambda$. Considérons $P_1 = (omega, restr(u, F_0)(omega))$. Considérons $P_1 = (omega,restr(u, F_0)(omega))$.

    $P_1$ est un plan car $restr(u, F_0)$ n'a pas de valeur propre réelle ($omega$ et $restr(u, F_0)(omega)$ ne sont pas colinéaires car $u$ n'admet pas de valeurs propres.)

    $P_1$ est stable par $restr(u, F_0)$ :

    On a $v_0(omega) = restr(u, F_0)(omega) + restr(u^*, F_0)(omega)$. Appliquons $restr(u, F_0)$ à cette équation :

    $restr(u, F_0)(lambda omega) = lambda restr(u, F_0)(omega) = restr(u^2, F_0)(omega) + (restr(u, F_0) compose restr(u^*, F_0))(omega) quad (*)$

    Mais $restr(u, F_0) compose restr(u^*, F_0) = restr(Id, F_0)$ car $restr(u^*, F_0) = u^(-1)(F_0)$ (car $u in O(n)$)

    $(*)$ donne $restr(u^2, F_0)(omega) = lambda restr(u, F_0)(omega) - omega in P_1$

    La restriction $restr(u, P_1)$ est un endomorphisme orthogonal de $P_1$ sans valeur propre réelle, $restr(u, P_1)$ est une rotation d'angle $theta_1 in.not pi ZZ$. On considère ensuite $P_1^perp$ dans $F_0$ et on itère le processus. On continue ainsi jusqu'à épuisement de la dimension de $F_0$.
]

== Décomposition polaire et valeurs singulières

#definition[
  Soit $E$ un espace euclidien, un endomorphisme $u in Lin(E)$ *symétrique* est dit positif si : $forall x in E$, $scal2(u(x), x) >= 0$

  Il est dit #underline[défini positif] si $forall x != 0_E in E$, $scal2(u(x), x) > 0$
]

#proposition[
  Avec les mêmes notations :
  + $u$ est positif #underline[si, et seulement si], ses valeurs propres sont positives ou nulles.
  + $u$ est défini positif si, et seulement si, ses valeurs propres sont strictement positives
]

#proof[
  + Soit $BBB = (e_1, dots, e_n)$ une base orthomormale de vecteurs propres diagonalisant $u$. Notons $lambda_i$ la valeur propre associée à $e_i$ pour $i = 1, dots, n$.
    Si $x = sum_(i = 1)^n x_i e_i$, alors $u(x) = sum_(i = 1)^n x_i u(e_i) = sum_(i = 1)^n lambda_i x_i e_i$. On a :

    $scal2(u(x), x) = scal2(sum_(i=1)^n x_i e_i, sum_(j=1)^n x_j e_j) = sum_(i,j = 1)^n lambda_i x_i x_j underbrace(scal2(e_i, e_j), =delta_(i j)) = sum_(i=1)^n lambda_i x_i^2$

    Si toutes les valeurs propres $lambda_i$ sont positives, $scal2(u(x), x) >= 0$. Réciproquement, s'il existe une valeur propre strictement négative, par exemple $lambda_1$, alors $scal2(u(e_1), e_1) = lambda_1 < 0$ et $u$ n'est pas positif.
  + Le raisonnement est analogue avec le cas strictement positif.
]

#proposition[
  Soit $u$ un endomorphisme auto-adjoint défini positif d'un espace euclidien $E$.

  Il existe un #underline[unique] endomorphisme auto-adjoint #underline[défini positif] tel que $v^2 = v compose v = u$.

  On dit que $v$ est la #underline[racine carrée] positive de $u$.
]

#proof[
  Soit $(e_1,dots,e_n)$ une base orthonormale  de $E$ diagonalisant $u$, $Sp u = (lambda_1,dots,lambda_n)$ (rq : on peut avoir $lambda_i = lambda_j$ avec $i != j$).

  On a $lambda_i > 0$ pour tout $i in [|1,n|]$. Définissons $v$ par sa matrice dans la base $(e_1,dots,e_n)$.
  $
    Mat_(e_i)(v) = mat(sqrt(lambda_1), dots, 0; vdots, ddots, vdots; 0, dots, sqrt(lambda_n))
  $

  On a $v^2 = v compose v = u$ et $v$ est auto-adjoint défini positif.

  #underline[Pour l'unicité] : s'il existe $w$ auto-adjoint défini positif tel que $w^2 = u$, en le diagonalisant dans une base orthonormale, on voit que $u$ est aussi diagonale dans la même base et dont que $w = v$.
]

#proposition[
  Soit $f$ in $GL(E)$ ($f$ est un automorphisme de $E$)

  Alors $f^* compose f$ est auto-adjoint et défini positif.
]

#proof[
  $(f^* compose f)^* = f^* compose f^(**) = f^* compose f, f^* compose f$ est symétrique.

  $forall x in E without {0}, scal2((f^* compose f)(x), x) = scal2(f(x), f(x)) = norm(f(x))^2 > 0$ car $Ker f = {0}$
]

#theorem("Décomposition polaire")[
  Soit $f in GL(E)$. Il existe un unique couple $(u,h)$ d'endomorphismes de $E$ avec $u$ orthogonal et $h$ symétrique défini positif tel que $f = u compose h$.
]
#theorem("Décomposition polaire version matricielle")[
  Si $A in GL_n (RR), exists!(U,H) in O(n) times SSS_n^(+)(RR)$ tel que $A = U H$

  $SSS_n^+(RR)$ et l'ensemble des matrices de $M_n (RR)$ symétriques à valeurs propres strictement positives.
]

#proof[
  #underline[Existence] : Soit $h$ la racine carrée positive de $f^* compose f$ (qui est symétrique définie positive par la proposition précédente). Posons $u = f compose h^(-1)$ ($h$ étant définie positive, il est inversible)

  Montrons que $u in O(E)$. On aura le résultat car $f = u compose h$.

  $
    u^* compose u &= (f compose h^(-1))^* compose (f compose h^(-1)) = (h^*)^(-1) compose f^* compose f compose h^(-1) = h^(-1) compose (f^* compose f) compose h^(-1) \
    &= h^(-1) compose h^2 compose h^(-1) = Id_E
  $

  #underline[Unicité] : Si $f = u compose h$, $f^* compose f = (u compose h)^* compose (u compose h) = h^* compose (u^* compose u) compose h = h compose Id_E compose h = h^2$ et $h$ est l'unique racine carrée positive de $f^* compose f$. Du coup $u = f compose h^(-1)$ est uniquement défini.
]

== Décomposition en valeurs singulières

Soit $A in M_(m,n)(RR)$

On rappelle que $transp(A)A in M_n (RR)$ est symétrique positive.

#definition[
  On appelle valeurs singulières de $A in M_(m,n) (RR)$ les racines carrées positives des valeurs propres strictement positives de $transp(A)A$
]
#remark("⚠️")[
  Les valeurs singulières ne concernent pas la valeur propre $0$.
]

#theorem[
  Soit $A in M_(m,n)(RR)$, il existe $U in O(m), V in O(n)$ et $Sigma$ une matrice "diagonale", $Sigma in M_(m,n)(RR)$ formée par les valeurs singulières de $A$ telles que $A = underbrace(U, in M_(m,m)(RR)) underbrace(sigma, in M_(m,n)(RR)) underbrace(transp(V), in M_(n,n)(RR))$

  "diagonale" signifie que dans $Sigma$, les valeurs singulières sont les premiers éléments de la diagonale, les autres étant nuls
]

#example[
  Avec $m < n$, $mat(1, 0, 0; 0, 2, 0)$, $mat(1, 0, 0; 0, 0, 0)$ sont diagonales

  Avec $m > n$, $mat(1, 0; 0, 2; 0, 0)$, $mat(1, 0; 0, 0; 0, 0)$ sont diagonales
]

#remark[
  On peut montrer :
  + Les valeurs singulières sont les racines carrées positives des valeurs propres strictement positives de $transp(A)A$ et de $transp(A)A$
  + $U$ est la matrice des vecteurs propres de $A transp(A)$
  + $V$ est la matrice des vecteurs propres de $transp(A)A$
]

#proof("du théorème")[
  Soit $A in M_(m,n)(RR)$

  $transp(A)A in M_(n)(RR)$, $transp(A)A$ symétrique positive donc diagonalisable.

  Supposons $Sp(transp(A)A) = {lambda_1,dots,lambda_n}$

  On suppose que $lambda_1 >= lambda_2 >= ... >= lambda_r > 0$ et $lambda_(r+1), dots,lambda_n = 0$

  Prenons $(v_1,dots,v_n)$ une base #underline[orthonormale] de vecteurs propres (théorème spectral).

  C'est-à-dire : $forall i = 1,dots,n$, $transp(A)A v_i = lambda_i v_i$

  #underline[Remarque :] $transp(v_i)transp(A)A v_j = scal2(v_i, transp(A)A v_j) = scal2(v_i, lambda_j v_j) = lambda_j delta_(i j)$

  On pose $sigma_i = sqrt(lambda_i)$ et $u_i = 1/sigma_i A v_i$ pour $i in [|1,r|]$

  $(u_1,dots,u_r)$ est une famille orthonormée de $RR^n$

  En effet, $forall i,j in [|1,r|]$ :
  $
    scal2(u_i, u_j) = 1/(sigma_i sigma_j) scal2(A v_i, A v_j) = 1/(sigma_i sigma_j) scal2(transp(A)A v_i, v_j) = lambda_i/(sigma_i sigma_j) scal2(v_i, v_j) = sigma_i/sigma_j delta_(i j)
  $

  Qui est bien orthonormée.

  Complétons la famille $(u_1,dots,u_r)$ en une base $(u_1,dots,u_n)$ orthonormée de $RR^n$.

  Notons $U$ la matrice de passage de la base canonique de $RR^n$ à $(u_1,dots,u_n)$,

  ainsi que $V$ la matrice de passage de la b.c. à $(v_1,dots,v_n)$

  #underline[Remarque :] $U$ et $V$ sont orthogonales.

  Considérons la matrice $underbrace(transp(U), (n times m))underbrace(A, (m times n)) underbrace(V, (n times n)) in M_(m,n)(RR)$

  $(transp(U) A V)_(i j) = transp(u_i) (A v_j)$

  Si $j <= r$, $A v_j = sigma_j u_j$ donc $transp(u_i) A v_j = 1/sigma_i transp((A v_i))A v_j$

  $transp(u_i)A v_j = 1/sigma_i transp(v_i)transp(A)A v_j = lambda_j/sigma_i transp(v_i)v_j = lambda_j/sigma_i lambda_(i j)$

  soit si $i = j$, $transp(u_i)A v_i = sigma_i^2/sigma_i = sigma_i$ et si $i != j, transp(u_i)A v_j = 0$

  Si $j > r$ :

  #underline[Remarque :] on a $Ker f = Ker (f^* compose f)$ pour $f$ une application linéaire (ici $f : RR^n --> RR^m$)

  On a clairement que $Ker f subset Ker(f^* compose f)$

  Pour l'inclusion inverse : Soit $x in Ker(f^* compose f)$, alors :
  $ 0 = scal2((f^* compose f)(x), x) = scal2(f(x), f(x)) = norm(f(x))^2 $ donc $x in Ker f$

  Si $j > r$, $transp(A)A v_j = 0$ donc $A v_j = 0$, ainsi $transp(u_i)A v_j = 0$

  On a bien que $transp(U)A V = Sigma$ diagonale donnée dans le théorème.

]

= Formes quadratiques

Dans ce chapitre, $K$ sera un corps de caractéristique différente de $2$. (Disons $K$ = $RR$ ou $CC$)

== Généralités et Orthogonalité

#property("Rappel")[
  À toute forme bilinéaire $f : E times E --> K$, on associe une unique application linéaire de $E$ dans $E^*$ ($E$ est un $K$-espace vectoriel)

  $L : application(E, E^*, y, L(f)(y) : application(E, K, x, L(f)(y)(x) = f(x,y)))$
]

#remark[
  On pouvait aussi définir
  $
    R(f) : application(E, E^*, x, R(f)(x) : application(E, K, y, f(x,y)))
  $
]

#definition[
  Soit $E$ un $K$-espace vectoriel muni d'une forme bilinéaire $f$.
  + On appelle noyau (à droite) de $f$ l'ensemble
    $
      E^perp = {y in E | f(x,y) = 0 quad forall x in E}
    $
  + On appelle noyau à gauche de $f$ l'ensemble
    $
      lperp(E) = {x in E | f(x,y) = 0 quad forall y in E}
    $
]

#remark[
  + $E^perp$ et $lperp(E)$ sont des $K$-espaces vectoriels
  + Si $E$ est de dimension finie, muni d'une base $EEE = (e_1,dots,e_n)$, notons $A = (f(e_i,e_j))_(1<=i,j<=n)$ sa matrice. Si $X$ et $Y$ sont les vecteurs colonne représentant respectivement des vecteurs $x,y$ de $E$ (dans la base $EEE$)

    $f(x,y) = transp(X)A Y$
    - Si $x in lperp(E)$, $forall y in E$, $transp(X)A Y = 0 <==> transp(A) X = 0$

    Le noyau à gauche est le noyau de la matrice $transp(A)$ (c'est le noyau de l'application $R(f)$)
    - Si $y in E^perp$, $forall x in E$ : $transp(X)A Y = 0 <==> A Y = 0$

      Le noyau à droite est le noyau de la matrice A (c'est le noyau de l'application $L(f)$)
  + Si $f$ est symétrique, $E^perp = lperp(E)$
]

#definition[
  Une forme bilinéaire $f$ sur $E$ est dite non-dégénérée à droite (resp. à gauche) si $E^perp = {0_E}$ (resp. $lperp(E) = {0_E}$).

  Elle est dite non-dégénérée si elle est non-dégénérée à droite et à gauche.
]

#remark[
  + "$f$ est non-dégénérée à droite" équivaut à dire que $L(f)$ est injective
  + Si $f$ est symétrique, non-dégénérée à droite équivaut à non-dégénérée à gauche, et en dimension finie ($det A = det(transp(A))$)
  + ⚠️ même si $f$ est symétrique positive ($K = RR$), dire que $f$ est non-dégénérée n'implique pas que $f$ est un produit scalaire.
]
#definition[
  Si $E$ est un $KK-$espace vectoriel et $f$ une forme bilinéaire symétrique, on appelle *rang de $f$*, noté $Rg f$, le rang de la matrice de $f$ dans une base quelconque de $E$.

  On a montre le théorème suivant :
]

#theorem[
  Soit $f$ une forme bilinéaire sur un $K$-espace vectoriel $E$ de dimension finie,

  $f$ est non-dégénérée ssi le déterminant de sa matrice dans une base quelconque est non-nul.
]

#definition[
  Soit $F$ un sous-espace vectoriel de $E$. On appelle :
  - Orthogonal à droite de $F : F^perp = {y in E | f(x,y) = 0 quad forall x in F}$
  - Orthogonal à gauche de $F$ : $lperp(F) = {x in E | f(x,y) = 0 quad forall y in F}$
]

#remark[
  $F^perp$ et $lperp(F)$ sont des sous-espaces vectoriels de $E$.
]

#theorem[
  Soit $f$ une forme bilinéaire #underline[non-dégénérée] sur $E$, $E$ étant de dimension finie $n$. Alors $dim F + dim F^perp = dim E$
]

#proof[
  Dire que $y in F^perp$ signifie que $L(f)(y) in E^*$ s'annule sur $F$.

  Réciproquement, si $phi in E^*$ s'annule sur $F$, comme $L(f)$ est un isomorphisme, il existe $y in E$ tel que $phi = L(f)(y)$ ($L(f)$ est injective car $f$ est non-degénérée)

  On conclut que $F^perp$ est en bijection avec l'ensemble des formes linéaires s'annulant sur $F$ et $dim F^perp = n - dim F$

  Attention : même si $f$ est non-dégénérée, $F$ et $F^perp$ ne sont pas toujours en somme directe.
]

#example[
  $E = RR^2, f$ définie par sa matrice $mat(1, 0; 0, -1) = A$. $det(A) != 0$ donc $f$ est symétrique non-dégénérée.

  #underline[Remarque :] Si $x = (x_1,x_2), y = (y_1,y_2)$, alors $f(x,y = x_1 y_1 - x_2 y_2)$

  Soit $F = Vect((1,1))$

  $F^perp = {x in RR^2 | f(x,y) = 0 quad forall y in F} = {(x_1, x_2) in RR^2 | x_1 - x_2 = 0} = F$

  on a bien $dim F + dim F^perp = 1 + 1 = 2$ mais $f(1,1) = 0$ donc $F inter F^perp != {0_E}$
]

#theorem[
  Soit $f$ une forme bilinéaire non-dégénérée sur un espace $E$ de dimension finie et soit $F$ un sous-espace vectoriel de $E$. Les assertions sont équivalentes :
  + $F inter F^perp = {0}$
  + $E = F osum F^perp$
  + la restriction $restr(f, F)$ de $f$ à $F times F$ est #underline[non-dégénérée].
]
#proof[

  $a) <==> b)$ est immédiat.

  Montrons $a) ==> c)$ par contraposée. Si $restr(L(f), F) : F --> F^*$ n'est pas injective, il existe $y in F$ non-nul tel que pour tout $x in F$ $restr(L(F), F)(y)(x) = 0$ donc c$y in F inter F^perp$ ce qui contredit $a)$.

  Montrons $c) ==> b)$. Soit $y in E$, considérons la forme linéaire $phi_y : application(F, K, x, f(x,y))$

  Comme $L(restr(f, F))$ est bijective ($restr(f, F)$ est non-dégénérée), il existe un unique $y^' in F$ tel que $phi_y = L(restr(f, F)(y^'))$

  $forall x in F, L(restr(f, F))(y^') = f(x,y^') = f(x,y) = phi_y (x)$, $forall x in F$.

  Donc $f(x,y-y^') = 0$, $forall x in F$ et $y-y^' in F$, et $y - y^' in F^perp$ et $y = (y - y^') + y^'$

  Cette décomposition est unique car si $y = u + v$ avec $u in F, v in F^perp$

  $forall x in F, f(x,y) = f(x,u + v) = f(x,u) + cancel(f(x,v)) = f(x,u) = f(x,y^')$

  donc $L(restr(f, F))(u) = L(restr(f, F))(y^')$ donc $u = y^'$ par injectivité de $L(restr(f, F))$

]

_De manière générale, on a :_
#proposition(["Pour la culture"])[
  Soit $f$ une forme bilinéaire #underline[symétrique] sur $E$ un espace de dimension finie et soit $F$ un sous-espace vectoriel de $E$.

  $dim E = dim F + dim F^perp - dim(E^perp inter F)$
]

#proof[
  Considérons la restriction à $F$ de l'application linéaire $L(f) : E --> E^*$, $restr(L(f), F) : F --> E^*$.

  Par le théorème du rang, $dim F = dim Ker(restr(L(f), F)) + dim Im(restr(L(f), F))$
  $
    Ker(restr(L(f), F)) = {y in F | f(x,y) = 0 quad forall x in E} =E^perp inter F
  $

  Comme nous sommes en dimension finie, $E$ est isomorphe à $E^(**)$. $restr(L(f), F)(F)$ est un sous-espace vectoriel de $E^*$, sa dimension est égale à $dim(E^*) - dim(A)$ où $A$ est le sous-espace vectoriel de $E^(**)$ des formes linéaires sur $E^*$ s'annulant sur $restr(L(f), F)(F)$

  $
    A = {x in E^** isommorphic E | phi(x) = 0, forall phi in restr(L(f), F)(F)} = {x in E | f(x,y) = 0 quad forall y in F} = F^perp
  $
  Donc $dim Im(restr(L(f), F)) = dim E - dim F^perp$

  D'où le résultat : $dim F = dim(E^perp inter F) + dim E - dim F^perp$ et $dim E = dim F + dim F^perp - dim(E^perp inter F)$
]

== Généralités sur les formes quadratiques

#definition[
  Une application $q : E --> K$ est appelée forme quadratique sur $E$ si il existe une forme bilinéaire *symétrique* $f$ sur $E$ telle que $forall x in E, q(x) = f(x,x)$
]

La formule de polarisation nous montre que la forme bilinéaire symétrique, qu'on appelle #underline[forme polaire], associée à une forme quadratique est unique.

Rappel :
#proposition("Formules de polarisation")[
  Soit $q$ une forme quadratique sur $E$ de forme polaire $f$. Alors pour tout $x,y in E$ :
  + $f(x,y) = 1/2 (q(x+y) - q(x) - q(y))$
  + $f(x,y) = 1/4 [q(x+y)-q(x-y)]$
]

#remark[
  Une forme quadratique est donnée par un polynôme homogène de degré 2
]


#definition[
  Si $E$ est de dimension finie, muni d'une forme quadratique $q$, on appelle matrice de $q$ la matrice de sa forme polaire et si $(e_1,dots,e_n)$ est une base de $E$, $A = (f(e_i,e_j))_(1<=i,j<=n) in M_n (K)$ la matrice e $f$, $e = sum_(i=1)^n x_i e_i$, $X = vec(x_1, vdots, x_n)$, $q(x) = transp(X)A X$
]

#example[
  $E = RR^3$, $q(x_1,x_2,x_3) = 7x_1^2 + 6x_1 x_2 + 5 x_2 x_3$

  La matrice de $q$ dans la base canonique de $RR^3$ est $mat(7, 3, 0; 3, 0, 5/2; 0, 5/2, 0)$
]

#remark[
  L'application qui associe à une forme quadratique sa forme polaire est un isomorphisme de $K$-espace vectoriel.
]

#exercice[ Faire la preuve ]

#definition[
  Soit $q$ une forme quadratique sur $E$ et $f$ sa forme polaire.
  + - On appelle *noyau* de $q$ le noyau de $f$
    - $q$ est dite *non-dégénérée* si $f$ est non-dégénérée
    - Si $E$ est de dimension finie, Le rang de $q$ est $Rg q = Rg f = dim E - dim Ker q$.
  + On vecteur $x$ de $E$ est dit *isotrope* si $q(x) = 0$. L'ensemble des vecteurs isotropes de $E$ pour $q$ est appelé #underline[cône isotrope] $C(q)$.
  + $q$ est *définie* si $C(q) = {0_E}$
]

#remark[
  On a $Ker q subset C(q)$ mais on n'a généralement pas égalité.

  De plus, $C(q)$ n'est, en général, pas un espace vectoriel.

  On a : $q$ défini $==> q$ non-dégénéré, mais pas l'inverse.
]

#example[
  + Un produit scalaire $f$ est défini (et non-dégénéré). Pour $q$ la forme quadratique associé à $f$,
    $
      Ker(q) = C(q) = {0_E}
    $
  + $E = RR^2$, $q(x_1,x_2) = x_1^2 - x_2^2$. $M(q) = mat(1, 0; 0, -1)$

    $Ker q = {0_E}$, $q$ est non-dégénérée.

    $C(q) = {(x_1,x_2) in RR^2 | x_1^2 - x_2^2 = 0} = {(x_1,x_2) in RR^2 | x_1 = x_2 or x_1 = -x_2}$ est la réunion de deux droites vectorielles (on voit aussi qu'il n'est pas un espace vectoriel). $q$ est #underline[non-définie].
  + $E = RR^3$, $q(x_1,x_2,x_3) = 2x_1^2 + x_2^2 + x_3^2 + x_1x_2$
    $
      Mat(q) = mat(2, 1/2, 0; 1/2, 1, 0; 0, 0, 1)
    $
    $Ker q = {0_E}$, $q$ est non-dégénérée.
  + $E = RR^3$, $q(x_1,x_2,x_3) = x_1^2 - x_3^2$, $M(q) = mat(1, 0, 0; 0, 0, 0; 0, 0, -1)$

    $Ker q = Vect((0,1,0))$, $q$ est dégénérée.

    $C(q) = {(x_1,x_2,x_3) in RR^3 | x_1^2 - x_3^2 = 0} = {(x_1,x_2,x_3) in RR^3 | x_1 = x_3 or x_1 = -x_3}$ est la réunion de deux plans. $q$ dégénérée $==>$ $q$ non-définie.
]

#definition[
  On dit qu'une famille $(e_1,dots,e_p)$ de vecteurs de $E$ est orthogonale si $f(e_i,e_j) = 0$, $forall i!=j$ avec $1<= i,j <= p$

  (Rq : pas besoin d'avoir $f(e_i,e_i) != 0$)
]
#theorem[
  Soit $f$ une forme bilinéaire symétrique sur $E$ de dimension finie.

  Alors $E$ admet une base orthogonale pour $f$.
]

#proof[
  Soit $q$ la forme quadratique associée à $f$.

  Si $q = 0$, toute base de $E$ est orthogonale pour $f$.

  Supposons $q != 0$, faisons une récurrence sur $dim E = n$
  + Si $n = 1$, rien à dire.
  + Supposons que tout $K$-espace vectoriel muni d'une forme quadratique de dimension $<=n$ admet une base orthogonale pour $q$.
    Soit $E$ de dimension $n+1$ muni d'une forme quadratique $q$ non nulle de forme polaire $f$.
    + Si $Ker f != {0_E}$, on choisit $F$ un supplémentaire de $Ker f$ dans $E$, que l'on munit de la forme quadratique $restr(q, F)$
      Par hypothèse de récurrence, $F$ admet une base orthogonale pour $restr(q, F)$, que l'on complète par une base de $Ker f$. C'est une base orthogonale de $E$.
    + Si $Ker f = {0_E}$, prenons $e_1 in.not C(q)$ (possible car $q != 0$). On note $F = Vect(e_1)^perp$. Comme $q$ est non-dégénérée, $dim F + dim Vect(e_1) = dim E = n+1$.

      On a même que $E = F osum Vect(e_1)$ car $e_1 in.not Vect(e_1)^perp$  ($e_1 in.not C(q)$)

      On applique l'hypothèse de récurrence à $F$ muni de $restr(q, F)$ : il existe une base $(e_2,dots,e_(n+1))$ de $F$ orthogonale pur $restr(q, F)$. $(e_1,dots,e_(n+1))$ est une base de $E$ orthogonale pour $q$.


  D'où le résultat.
]
// À dmd à la prof..? : Pourquoi on ne peut pas simplement faire la preuve en disant que M(q) est diagonalisable sur une base B orthogonale par f puisqu'elle est symétrique ?

#corollary[
  Soit $A in M_n (K)$ symétrique, il existe une matrice $P in GL_n (K)$ telle que $transp(P)A P$ soit diagonale.
]

L'algorithme de réduction de Gauss appliqué à une forme quadratique permet de trouver des bases orthogonales pour $q$. _Voir les exemples ci-dessous, ainsi que la méthode de Gauss expliquée plus haut, #underline[@methode_reduction_gauss]_

#example[

  E = $RR^3$, $q(x,y,z) = x^2 - 2y^2 + 6z^2 + 2x y - 4 x z + 4 y z$.
  On a $M(q) = mat(1, 1, -2; 1, -2, 2; -2, 2, 6)$.
  $
    q(x,y,z) & = (x^2 + 2 x y - 4 x z) - 2y^2 + 6z^2 + 4 y z \
             & = [(x+ (y-2z))^2 - (y-2z)^2]-2y^2 + 6z^2 + 4 y z \
             & = (x+y-2z)^2 - 3y^2 + 2z^2 + 8y z \
             & = (x+y-2z)^2 + 2(z^2 + 4 y z)^2 - 3 y^2 \
             & = (x+y-2z)^2 + 2[(z+2y)^2 - 4y^2]- 3y^2 \
             & = (x+y-2z)^2 + 2[(z+2y)^2 - 11y^2
  $

  En posant respectivement $X,Z,Y$, les 3 formes linéaires mises carré, on trouve $q(X,Y,Z) = X^2 - 11Y^2 + Z^2$. Donc $M_((X,Y,Z))(q) = mat(1, 0, 0; 0, -11, 0; 0, 0, 2)$

  On résout le système
  $
    cases(X = x + y - 2z, Y = y, Z = z + 2y) <==> cases(x = X - Y + 2Z - 4Y = X - 5Y + 2Z, y = Y, z = Z - 2Y)
  $

  Si un vecteur $u$ a pour coordonnées $(x,y,z)$ dans la base canonique et $(X,Y,Z)$ dans la base orthogonale cherchée, si $P$ désigne la matrice de passage de la base canonique à la base orthogonale, on a :
  $vec(x, y, z) = P cdot vec(X, Y, Z)$

  Ici, $P = mat(1, -5, 2; 0, 1, 0; 0, -2, 1)$, $u_1 = (1,0,0)$, $u_2 = (-5,1,-2)$, $u_3 = (2,0,1)$, $(u_1,u_2,u_3)$ est orthogonale à $q$.

  #underline[Autre méthode].

  Notons $(e_1,e_2,e_3)$ la base canonique de $RR^3$,

  $cases(l_1(x,y,z) = x+y-2z, l_2(x,y,z) = y)$. $(l_1,l_2,l_3)$ est une base de $(RR^3)^*$

  Écrivons : $cases(l_1 = e_1^* + e_2^* - 2e_3^*, l_2=e_2^*, l_3=2e_2^* + e_3^*)$.

  Notons $Q = mat(1, 0, 0; 1, 1, 2; -2, 0, 1)$ la matrice de passage de $(e_1^*,e_2^*,e_3^*)$ à $(l_1,l_2,l_3)$.

  La base orthogonale cherchée est la base antéduale de $(l_1,l_2,l_3)$.

  La matrice $P$ est donnée par $P = transp(Q^(-1)) = 1/det(Q) Comat(Q) = 1 cdot mat(+1, -5, +2; -0, +1, -0; +0, -2, +1)$

]

#example[
  $E = RR^3$, $q(x,y,z) = x^2 + 2y^2 + 8z^2 - 2x y + 4 x z$,

  $M(q) = mat(1, -1, 2; -1, 2, 0; 2, 0, 5)$ $q$ est dégénérée (on résout le système ou on prend le déterminant).

  $
    q(x,y,z) & = (x^2-2x y + 4 x z) + 2 y^2 + 8z^2 \
             & = [(x+(-y+2z))^2 - (-y+2z)^2]+2y^2 + 8z^2 \
             & = (x - y + 2z)^2 + y^2 + 4 z^2 + 4 y z \
             & = (x-y+2z)^2 + (y+2z)^2
  $
  On a $P^(-1) = mat(1, -1, 2; 0, 1, 2; 0, 0, 1)$
  Et :
  $
    cases(X = x-y+2z, Y = y + 2 z, Z=z)
    <==> cases(x = X + Y - 2Z - 2Z = X + Y - 4Z, y = Y - 2Z, z = Z)
  $
  donc $P = mat(1, 1, -4; 0, 1, -2; 0, 0, 1)$

  $cases(u_1 = (1,0,0), u_2 = (1,1,0), u_3 = (-4,-2,1))$ on a $(u_1,u_2,u_3)$ qui forme une base orthogonale pour $q$.

  #underline[Autre méthode :]

  $l_1(x,y,z) = x-y+2z ==> l_1 = e_1^* - e_2^* + 2e_3^*$

  $l_2(x,y,z) = y + 2 z ==> l_2 = e_2^* + 2e_3^*$

  $(l_1,l_2)$ est libre, on la complète en une base de $(RR^3)^*$ en posant $l_3 = e_3^*$

  $Q = mat(1, 0, 0; -1, 1, 0; 2, 2, 1)$ et $det(Q) = 1$

  $P = transp(Q^(-1)) = 1/det(Q) Comat(Q)$
]

#pagebreak()

_Cette page méthode ne provient pas d'un recopiage du cours mais de la synthèse que j'ai tiré des exemples_

#method("Trouver une base orthogonale pour une forme quadratique, vision matricielle")[
  - Appliquer la réduction de Gauss à $q$.
  - Puisque l'on a $q(x_1,dots,x_n) = (c_1 l_1^2 + ... + c_n l_n^2)(x_1,dots,x_n)$, on peut écrire :
    $ cases(X_1 = l_1(x_1,dots,x_n), vdots, X_n = l_n (x_1,dots,x_n)) $ en complétant le système si $q$ est dégénérée (= il y a moins de formes linéaires que dans la variable, cf @critere_def_pos_gauss), c'est-à-dire rajouter des équations de la forme $X_i = x_i$

  - Cela équivaut à écrire $vec(X_1, vdots, X_n) = P^(-1)vec(x_1, vdots, x_n)$ où $P$ est la matrice de passage de la base canonique à la base orthogonale cherchée dans laquelle les composantes des vecteurs sont les $X_i$.

    Ainsi, on inverse $P$ en trouvant les $x_i$ à partir des $X_j$, ou on inverse simplementent $P$ à la main.

  #v(1em)
  On a le résultat de l'orthogonalité car $q(X_1,dots,X_n) = c_1 X_1^2 + dots + c_n X_n^2$, donc :

  $M(q) = mat(c_1, , (0); , ddots, ; (0), , c_n)$ qui correspond bien à une base orthogonale pour $q$.

]

#method("2nde méthode, par une vision duale")[
  La méthode de Gauss nous donne une famille libre de formes linéaires $(l_1,dots,l_r)$ dans $E^*$ que l'on vient compléter par $(e_i^*)_(r+1<=i<=n)$ pour obtenir $BBB^*$, qui nous donne une base de $E^*$. On cherche donc $BBB$ l'antéduale de $BBB^*$, en utilisant $M_((e_i^*),(BBB^*))(Id_(E^*)) = transp((M_((e_i),BBB)(Id)^(-1)))$.
]

_Remarquons que la vision matricielle ne transpose pas alors que la vision duale le fait, c'est tout simplement car dans la première, on écrit naturellement le système $X = P^(-1)x$ avec les vecteurs en ligne, alors que pour correspondre à une vision duale on les range en colonne._

== Classification des formes quadratiques sur $CC$ et $RR$

#theorem[
  Soit $E$ un $CC$-espace vectoriel de dimension $n$ muni d'une forme quadratique $q$. Il existe un entier $r in [|0,n|]$ et une base $BBB = (epsilon_1,dots,epsilon_n)$ de $E$ orthogonale pour $q$ tels que : $q(epsilon_i) = 1$ pour $1 <= i <= r$ et $q(epsilon_i) = 0$ pour $r+1 <= i <= n$. L'entier $r$ est le rang de $q$ et ne dépend pas de $BBB$. Dans cette base, la matrice de $q$ est $mat(I_r, 0; 0, 0)$
]

#proof[
  Soit $EEE = (e_1,dots,e_n)$ une base $q$-orthogonale de $E$ et on pose $q(e_i) = a_i in CC$ pour $i = 1,...,n$

  Il est clair que le rang de $q$ est le nombre de scalaires $a_i$ non nuls. Supposons alors que $a_i != 0$ pour $1 <= i <= r$ et $a_i = 0$ pour $r+1 <= i <= n$.

  Pour $i = 1,dots,r$, on note $b_i$ une racine carrée de $a_i$. On pose $epsilon_i = 1/(b_i) e_i$ pour $1 <= i <= r$ et $epsilon_i = e_i$ pour $r+1 <= i <= n$. $(epsilon_1,dots,epsilon_n)$ est une base de $E$ orthogonale pour $q$ et $q(epsilon_i) = 1$ pour $1 <= i <= r$ et $q(epsilon_i) = 0$ pour $r+1 <= i <= n$.
]

#corollary[
  Soit $E$ un $CC$-espace vectoriel de dimension fini muni d'une forme quadratique $q$, $E$ admet une base orthonormale si $q$ est non-dégénérée (donc de rang maximal).
]

#theorem("Loi d'inertie de Sylvester")[
  Soit $E$ un $RR$-espace vectoriel de dimension $n$ muni d'une forme quadratique $q$. Il existe un couple d'entiers $(s,t) in NN^2$ et une base $BBB = (epsilon_1,dots,epsilon_n)$, $q$-orthogonale de $E$ tels que : $q(epsilon_i) = 1$ pour $1 <= i <= s$, $q(epsilon_i) = -1$ pour $s+1 <= i <= s+t$ et $q(epsilon_i) = 0$ pour $s+t+1 <= i <= n$.

  Le couple $(s,t)$ ne dépend pas de la base orthogonale choisie et $s+t = Rg q$.

  Dans la base $BBB$, la matrice de $q$ est $mat(I_s, 0, 0; 0, -I_t, 0; 0, 0, 0)$
]

#definition("Signature d'une forme quadratique")[
  Le couple $(s,t)$ est appelé signature de $q$ et est noté $sgn q = (s,t)$
]

#proof[
  Soit $EEE = (e_1,dots,e_n)$ une base $q$-orthogonale de $E$ et on pose $q(e_i) = a_i in RR, i = 1,...,n$.

  Supposons que $a_i > 0$, $i = 1,dots,s$, $a_i < 0$, $i = s+1,dots,s+t$, $a_i = 0, i = s+t+1,dots,n$

  On pose : $ cases(epsilon_i = 1/sqrt(a_i)e_i\, quad &1 <= i <= s, epsilon_i = 1/sqrt(-a_i)e_i\, quad &s+1 <= i <= s+t, epsilon_i = e_i\, quad &i > s+t) $

  Il reste à prouver l'unicité du couple $(s,t)$. Donnons une base $(f_1,dots,f_n)$, $q$-orthogonale de $E$ telle que :
  - $q(f_i) = 1, i = 1,dots,s^'$ et $q(f_i) = -1, i = s^'+1,dots,s^'+t^'$
  - $q(f_i) = 0, i > s^' + t^'$

  On pose : $F = Vect(epsilon_1, dots, epsilon_n)$, $G = Vect(f_(s+1), dots, f_n)$

  On a $F inter G = {0_E}$.

  En effet, si $x in F inter G$, $x = sum_(i=1)^s x_i epsilon_i = sum_(s^'+1)_{i=s^'+1}^{s^'+t^'} y_i f_i$

  $q(x) = sum_(i=1)^n x_i^2 = sum_(i=1)^n x_i^2 = sum_(j=s^'+1)^(s^'+t^') - y_j^2$, donc $q(x) = 0$, ainsi $x_i = 0$ pour tout $i=1,dots,n$ et donc $x = 0_E$.

  On a $F osum G$.

  $dim(F + G) = dim F + dim G <= n$. Soit $s + n - s^' <= n$ ou encore $s <= s^'$

  en faisant de même pour $F = Vect(f_1, dots, f_s)$ et $G = Vect(epsilon_(s+1), dots, epsilon_n)$, on trouve $s^' <= s$. Au final $s = s^'$. Comme $Rg q = s+t = s^' + t^'$, on a $t = t^'$. D'où le résultat.
]

#corollary[
  $E$, un $RR$-espace vectoriel muni d'une forme quadratique $q$ admet une base orthonormale si, et seulement si, $sgn(q) = (n,0)$. (i.e. est un produit scalaire).
]

#remark[
  + $q$ est positive si $sgn(q) = (r,0)$, $r <= n$
  + $q$ est negative si $sgn(q) = (0,r)$, $r <= n$
  + $q$ est définie positive si $sgn(q) = (n,0)$
  + $q$ est définie négative si $sgn(q) = (0,n)$
]

== Groupe orthogonal associé à une forme quadratique

#proposition[
  Soit $E$ un $K$-espace vectoriel de dimension finie muni d'une forme quadratique $q$ non-dégénérée (de forme polaire $f$). Soit $u$ un endomorphisme de $E$, il existe un unique endomorphisme $u^*$ de $E$, appelé adjoint de $u$ tel que $forall x,y in E, f(u(x),y) = f(x,u^*(y))$
]

#proof[
  cf théorème de représentation de Riesz @riesz

  $L(f) : application(E, E^*, y, L(f)(y) : application(E, K, x, f(x,y)))$ est un isomorphisme si $f$ est non-dégénérée.

  Attention : Nous n'avons pas de base orthonormale, matriciellement, notons :

  $EEE = (e_1,dots,e_n)$ une base de $E$, $A$ la matrice de $q$ dans la base $EEE$, $M$ la matrice de $u$ dans la base $EEE$, $M^*$ la matrice de $u^*$ dans la base $EEE$.

  Posons $x = sum_(i = 1)^n x_i e_i$, $y = sum_(i=1)^n y_i e_i$, $X = vec(x_1, vdots, x_n)$, $Y = vec(y_1, vdots, y_n)$

  L'équation $(*) : f(u(x),y) = f(x,u^*(y))$ donne :
  $
    transp((M X)) A Y = transp(X) A M^* Y
    <==> transp(X) (transp(M)A) Y = transp(X) (A M^*) Y
  $
  soit $transp(M) A = A M^*$ ou encore $A^(-1)transp(M)A = M^*$.

  L'isomorphisme $L(f)$ garantit l'unicité de l'endomorphisme, et cette relation matricielle assure son existence.
]

On a les mêmes propriétés que précédemment pour l'adjoint d'un endomorphisme.

On peut donc définir le groupe orthogonal associé à $q$ non-dégénérée, c'est-à-dire l'ensemble des endomorphismes vérifiant $q(u(x)) = q(x), forall x in E$.

#remark[
  Dans le cadre de la relativité d'Einstein, $q(x) = x_1^2 + x_2^2 + x_3^2 - x_4^2$. Le groupe orthogonal associé à $q$ s'appelle groupe de Lorentz.
]

#proposition[
  Soient $E$ un $K$-espace vectoriel de dimension finie, $q$ une forme quadratique non-dégénérée de forme polaire $f$ sur $E$, $u$ un endomorphisme de $E$, on a équivalence entre :
  + $u$ est orthogonal pour $q$, i.e. $q(u(x)) = q(x), forall x in E$.
  + $f(u(x),u(y)) = f(x,y)$
  + $u^* compose u = Id_E$
]

_Les 2 équivalences restantes dans la proposition précédente nécessitaient une base orthonormale, que l'on n'a pas ici._

#proof[
  cf espaces euclidiens.
]
#remark[
  Soient $EEE = (e_1,dots,e_n)$ une base de $E$, $A$ la matrice de $q$ dans la base $EEE$, $M$ la matrice de $u$ dans la base $EEE$. Alors $u in O(q) <==> transp(M) A M = A$
]

#proof[
  En effet, écrivons $f(u(x),u(y)) = f(x,y)$ :
  $
    transp((M X))A M Y = transp(X)A Y <==> transp(X) (transp(M) A M) Y = transp(X)A Y
  $
]

= Espaces hermitiens

Mettons en lumière le problème :

Soit $B : application(E times E, CC, (x,y), sum_(i=1)^n x_i y_i)$

Mais $B(x,x) = sum_(i=1)^n x_i^2$, cela n'a pas de sens car $x_i^2$ n'est pas un nombre réel, et $B(x,x)$ peut valoir $0$ sans que $x$ ne valle $0$. Donc on n'a pas du tout de produit scalaire.

Par contre en posant $B(x,y) = sum_(i=1)^n bar(x_i) y_i$, on trouve des propriétés bien plus proches du produit scalaire puisque $B(x,x) = sum_(i=1)^n abs(x_i)$.

Dans ce chapitre, $E$ sera un $CC$-espace vectoriel de dimension finie.

== Produit scalaire hermitien

#definition[
  On dit que $f : E times E --> CC$ est une forme *sesquilinéaire* si :
  + $f$ est antilinéaire (ou semi-linéaire) par rapport à sa première variable, i.e. :
    $forall y in E, forall x_1,x_2 in E, forall lambda in CC$,
    $
      f(lambda x_1 + x_2, y) = bar(lambda) f(x_1,y) + f(x_2,y)
    $
  + $f$ est linéaire par rapport à sa seconde variable, i.e. :
    $forall x in E, forall y_1,y_2 in E, forall mu in CC$,
    $
      f(x, mu y_1 + y_2) = mu f(x,y_1) + f(x,y_2)
    $
]

#example[
  $E = CC^3$, $s(x,y) = bar(x_1)y_1 + 2 i bar(x_2)y_2 + (4-2i)bar(x_1)y_3 + 5 bar(x_2)y_3$ est sesquilinéaire

  _Rq : elle n'est pas hermitienne, voir plus loins_
]

Soit $EEE = (e_1,dots,e_n)$ une base de $E$, on note $a_(i j) = f(e_i, e_j), forall i,j = 1,dots,n$, $A = (a_(i j))_(1<=i,j<=n) in M_n (CC)$ est la matrice associée à la forme sesquilinéaire $f$ dans la base $EEE$.

Matriciellement, $f(x,y) = transp(bar(X))A Y$, où pour $x = sum_(i=1)^n x_i e_i$ et $X = vec(x_1,vdots,x_n)$, on note $bar(X) = vec(bar(x_1),vdots,bar(x_n))$


#theorem("changement de bases")[
  Supposons $E$ muni des bases $EEE$ et $EEE^'$, notons $P$ la matrice de passage de $EEE$ à $EEE^'$, soit $f$ une forme sesquilinéaire sur $E$, de matrice $A$ dans la base $E$ et $A^'$ dans la base $EEE^'$, alors $A^' = transp(bar(P))A P$, où, pour $P = (p_(i j))_(1<=i,j<=n)$, $bar(P) = (bar(p_(i j)))_(1<=i,j<=n)$
]

#proof[
  Soit $EEE = (e_1,dots,e_n)$ et $EEE^' = (e_1',dots,e_n')$, $x = sum_(i=1)^n x_i e_i = sum_(i=1)^n x_i' e_i'$, $X = vec(x_1,vdots,x_n)$, $X^' = vec(x_1^',vdots,x^'_n)$

  alors : $forall x,y in E, f(x,y) = transp(bar(X))A Y = transp(bar(X^'))A^' Y^'$. 
  
  De plus, $X = P X^'$, $Y = P Y^'$. Donc :

  $f(x,y) = transp((bar(P X^')))A P Y^' = transp(bar(P)bar(X^'))A P Y^' = transp(bar(X^'))(transp(bar(P))A P)Y^'$
]

#definition("Caractère hermitien")[
  On dit qu'une forme sesquilinéaire $f$ est *hermitienne* si :
  $
  forall x,y in E, f(x,y) = bar(f(y,x))
  $
]

#example[
  + $E = CC^3,$
    
    $h(x,y) = bar(x_1)y_1 + 3 bar(x_2)y_2 + 2 bar(x_3)y_3 + (2+3i)bar(x_1)y_2 + (2-3 i)bar(x_2)y_1 + (1-5i)bar(x_2)y_3 + (1+5i)bar(x_3)y_2$ est hermitienne
  + $E = M_n (CC)$, $h(A,B) = tr(transp(bar(A))B)$
]

#remark[
  + Matriciellement, une forme sesquilinéaire $f$ est hermtienne si, et seulement si, sa matrice $A$ dans une base de $E$ vérifie $transp(bar(A)) = A$. On dit qu'une telle matrice est *hermitienne*.

    Puisque $transp(bar(A)) = A$, les éléments de la diagonale de $A$ sont réels.
  + Si $f$ est une forme hermitienne, $bar(f(x,x)) = f(x,x)$ pour tout $x in E$, donc $f(x,x) in RR, forall x in E$.
]

#proposition("Formule de polarisation")[
  L'application qui associe à toute forme hermitienne $f$ sur $E$, la forme quadratique $q$ définie par $q(x) = f(x,x)$ bijective et $f$ est appelée forme polaire.

  $
  f(x,y) = (q(x + y) - q(x - y))/4 - i (q(x + i y) - q(x - i y))/4
  $
]

#proof[
  $q(x+y) = f(x+y,x+y) = f(x,x) + f(x,y) + f(y,x) + f(y,y) = q(x) + f(x,y) + bar(f(x,y)) + q(y) = q(x) + 2 Re(f(x,y)) + q(y)$

  $q(x-y) = f(x-y,x-y) = f(x,x) - f(x,y) - f(y,x) + f(y,y) = q(x) - f(x,y) - bar(f(x,y)) + q(y) = q(x) - 2 Re(f(x,y)) + q(y)$

  $q(x+y) - q(x-y) = 4 Re(f(x,y))$

  $
  q(x + i y) &= f(x + i y, x + i y) = f(x,x + i y) - i f(y, x+ i y) \ 
  &= f(x,x) + i f(x,y) - i f(y,x) + f(y,y)  \ &= q(x) + i(f(x,y)-bar(f(x,y))) + q(y) \
  &= q(x) + i (2i Im(f(x,y))) + q(y)
  $
  
  $q(x - i y) &= f(x - i y, x - i y) = f(x,x - i y) + i f(y, x- i y)  \
  &= f(x,x) - i f(x,y) + i f(y,x) + f(y,y) \
  &= q(x) - i(f(x,y)-bar(f(x,y))) + q(y) \ 
  &= q(x) - i (2i Im(f(x,y))) + q(y)$

  $q(x+i y) - q(x-i y) = - 4 Im(f(x,y))$

  Donc $q(x+y) - q(x-y) -i (q(x+i y) + q(x-i y)) = 4 f(x,y)$

]
