#import "@local/doc_fac:0.1.0": *
#import "@local/utils:0.1.0": *

#show: doc_fac.with(title: "Notes de TD - 19/05/2026",numbering: "I 1 a i  ")

= TD 4
== Exo 8
+ Hypothèse : $u$ non-nul isotrope, càd $u != 0$ et $q(u) = 0$. et $u cancel(perp_B) v$ càd $B(u,v) != 0$
  + Supposons $v$ isotrope càd $q(v) = 0$. On cherche $w = alpha u + beta v$ avec $alpha,beta in KK$ tel que $q(w) != 0$. Alors $q(w) = B(w,w) = B(alpha u + beta v, alpha u + beta v) = alpha^2 B(u,u) + 2 alpha beta B(u,v) + beta^2 B(v,v) = 2 alpha beta B(u,v) + beta^2 B(v,v)$
    On peut prendre $alpha = beta = 1$, et on a bien $q(w) != 0$

  + Supposons $q(v) != 0$. On cherche $w^' = alpha u + beta v$ avec $beta != 0$ (car $w^'$ non-colinéaire à $u$) tel que $q(w^') = 0$. Sans perdre de généralité, on peut supposer $beta = 1$. Ainsi $w^' = alpha u + v$. On finit en utilisant $cases(q(w^') = 0,B(u,v) != 0)$
  $
  q(w^') =alpha^2q(u) + 2 alpha B(u,v)
  $
  et on trouve $alpha = - (q(v))/(2 B(u,v))$ convient

+ Discussion : En dim 2, si $(u,v)$ base de $E$ et $B$ forme bilinéaire sur $E$, alors $M_(u,v) (B) = mat(B(u,u),B(u,v);B(v,u),B(v,v)) = mat(q(u),B(u,v);B(v,u),q(v))$. Si $u$ et $v$ isotropes : $M_(u,v) (B) = mat(0,B(u,v);B(v,u),0)$.
  
  Si $B(u,v) != 0$ et quitte à changer $u$ par $u/B(u,v)$, on a $M_(u,v) (B) = mat(0,1;1,0)$. C'est ce que l'on appelle un *plan hyperbolique*. Supposons $(u,v)$ base canonique de $RR^2$, alors : 
  - $B(vec(x,y),vec(x^',y^')) = transp(vec(x,y))mat(0,1;1,0)vec(x,y) = x y^' + y x^'$
  - $q_B (vec(x,y)) = transp(vec(x,y))mat(0,1;1,0)vec(x,y) = 2 x y$


== Exo 10

#remark("Rappel")[
  Soit $q$ une forme quadratique sur $E$.

  On note :

  $
  i_+(q) = max Card { (e_i)_(1<=i<=r) "famille libre de "E" tq" q(e_i) > 0} \
  i_-(q) = max Card { (e_i)_(1<=i<=r) "famille libre de "E" tq" q(e_i) < 0}
  $
]

#remark("Utile pour le TD")[
  Soit $E$ un $RR$-ev.
  Supposons que $q(x) = sum_(i=1)^r l_i (x)^2 - sum_(j=r+1)^(r+s) l_j (x)^2$ avec $(l_1,dots,l_(r+s))$ famille libre de $E^*$.

  Alors $sgn(q) = (r,s) = (i_+(q),i_-(q))$

  Conséquence : pour calculer la signature, on effectue la reduction de Gauss et on compte les coefficients positifs et négatifs devant les carrés.

  Rappel : $Rg(q) = r + s = dim E - dim Ker q$
]
_On ne l'a pas encore vu en cours, ce n'est pas un oubli de ma part_

+ $q(x,y) = x y$
  - Par la formule de polarisation, $B_q ((x,y),(x^',y^')) = (q((x,y) + (x^',y^')) - q(x,y) - q(x^',y^'))/2 = ... = 1/2 (x y^') + 1/2 (x^' y)$
  - Signature :
    $
    q(x,y) = x y = ((x + y)/2)^2 - ((x-y)/2)^2
    $
    donc $sgn(q) = (1,1)$
  - Base $q$-orthogonale :
    On utilise la réduction de Gauss,
    
    #underline[Cas général :]

    Supposons $q(x) = sum_(i=1)^n l_i (x)^2 - sum_(i=r+1)^(r+s) l_i (x)^2$

    Si $r+s < dim E$m on complete la famille libre en une base $(l_1,dots,l_n)$.

    Une base $q$-orthogonale est donnéee par la base antéduale (= préduale) de $(l_1,dots,l_n)$

    Ainsi: $(C_1,dots,C_n) = vec(L_1,vdots,L_n)^2$

    Dans l'exo, on a: $vec(L_1,L_2) = mat(1/2,1/2;1/2,-1/2)$ donc $(C_1,C_2) = mat(1/2,1/2;1/2,-1/2)^(-1) = -2 mat(-1/2, 1/2;-1/2,1/2) = mat(1,1;1,-1)$

    Conclusion : $(vec(1,1),vec(1,-1))$ est $q$-orthogonale

+ Pour $q(x,y,z) = x^2 - 4 x y + y^2 + 2 y z - z^2$, on trouve, par exemple, $q(x,y,z) = (x-2y)^2 - (z-y)^2 - 4 y^2$, ainsi $sgn(q) = (1,2)$