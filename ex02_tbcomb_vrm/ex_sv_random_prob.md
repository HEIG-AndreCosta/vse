## Exercise 1

Soient deux variables x et y, nombres réels, générées aléatoirement dans l’intervalle [0, 100].
1. Quelle est la probabilité que x soit dans l’intervalle [10, 30] ?
   (30 - 10) / 100 = 2/10

2. Quelle est la probabilité que y soit dans l’intervalle [40, 80] ?
   (80 - 40) / 100 = 4/10


3. Quelle est la probabilité que y soit dans l’intervalle [30, 100] ?
    
   (100 - 30) / 100 = 7/10

4. Ajoutons l’implication que si x < 10 alors y < 30.
    - Quelle est la probabilité que x soit dans l’intervalle [0, 10] si le générateur génère aléatoirement des valeurs pour x et y et ne garde que les combinaisons respectant l’implication ?
    Car la partie x <= et y >= 30 n'existe plus (7%)
        3/93


5. Si maintenant nous ajoutons un ordre de résolution, faisant que x est généré avant y, que
ce passe-t-il ?
    1/10

6. Quelle est la probabilité que y soit dans l’intervalle [30, 100] si le générateur génère aléatoi-
rement des valeurs pour x et y et ne garde que les combinaisons respectant l’implication ?
    63/93

7. Si maintenant nous ajoutons un ordre de résolution, faisant que x est généré avant y, que
ce passe-t-il ?
    9/10 * 7/10 = 63/100 

## Exercise 2

Soient deux variables a et b, nombres réels, générées aléatoirement dans l’intervalle [0, 1000].
1. Quelle est la probabilité que a soit dans l’intervalle [0, 100] ?

1/10

2. Ajoutons une distribution de probabilité faisant que 10% du temps a < 10 et que 20% du temps b < 100.
    - Quelle est la probabilité que a soit dans l’intervalle [5, 10] ?

    5 / 100 = 5%

3. Quelle est la probabilité que b soit dans l’intervalle [500, 550] ?
    P(b >100) . P(b [500, 550] | b > 100) = 50/900 * 8/ 10 = 4.4%

4. Quelle est la probabilité que a soit dans l’intervalle [5, 10] ET que b soit dans l’intervalle [500, 550] ?

    5 /100 * 50/ 900 * 8 /10 = 1/450 = 0.2222%
    

5. Ajoutons l’implication que si a < 10 alors b < 100.
    - Quelle est la probabilité que a soit dans l’intervalle [0, 10] si le générateur génère aléatoirement des valeurs pour a et b selon les contraintes de distribution précédentes 
    et ne garde que les combinaisons respectant l’implication ?


    P(combinaisons valides) = 1 - P(a <10) * P(b > 100) = 1 - 1/10 * 4/5 = 1 - 4/50 = 46/50 = 0.92

    P(a < 10) . P(b < 100) / P(combinaison valides) =  0.1 * 0.2 / 0.92 = 0.021

6. Si maintenant nous ajoutons un ordre de résolution, faisant que a est généré avant b, que
ce passe-t-il ?
    
    10 / 100  = 10%

7. Quelle est la probabilité que b soit dans l’intervalle [500, 550] si le générateur génère aléa-
toirement des valeurs pour a et b selon les contraintes de distribution précédentes et ne
garde que les combinaisons respectant l’implication ?
    
    P(b [500; 550]) . P(a > 10) / P(combinaisons valides) = (9/10 * 4/5 * 50/900) / (46/50) = 1/23
    
    


8. Si maintenant nous ajoutons un ordre de résolution, faisant que a est généré avant b, que
ce passe-t-il ?
    
    P(b [500; 550]) . P(a > 10) = (9/10 * 4/5 * 50/900) = 1/25

9. Nous changeons maintenant les probabilités de distribution : 90% du temps a < 10 et
20% du temps b < 100. Quelle est la probabilité que b soit dans l’intervalle [500, 550]
si le générateur génère aléatoirement des valeurs pour a et b selon ces contraintes de
distribution et ne garde que les combinaisons respectant l’implication ?

    P(combinaisons valides) = 1 - P(a <10) * P(b > 100) = 1 - 9/10 * 4/5 = 1 - 36/50 = 14/50 = 0.28

    P(b [500; 550]) . P(a > 10) / P(combinaisons valides) = (1/10 * 4/5 * 50/900) / (14/50) = 1/63

10. Si maintenant nous ajoutons un ordre de résolution, faisant que a est généré avant b, que
ce passe-t-il  

    P(b [500; 550]) . P(a > 10) = (1/10 * 4/5 * 50/900) = 1/225
