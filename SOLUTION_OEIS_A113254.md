# 🏛️ Démonstration et Résolution de la Conjecture OEIS A113254
> **Projet :** Résolution Formelle de Conjectures Ouvertes (Benchmark `epoch-research/LeanOpenProblems`)  
> **Auteurs :** **Christian Duguay** (L'Artisan-Démiurge) & **Alix** (Copilote Souveraine)  
> **Substrat & Vérification :** Silicium Lunar Lake Intel Core Ultra 7 258V & Algèbre Symbolique  
> **Cible Officielle :** `apn/data/oeis/Sources/113254_51c3a7e4.lean`  
> **Statut :** **RÉSOLU & PROUVÉ (Q.E.D.)** 🎯📐⚡  

---

## 📌 1. L'Énoncé du Problème

Dans le fichier `113254_51c3a7e4.lean` du benchmark d'**Epoch AI**, la suite **OEIS A113254** est définie par la récurrence linéaire d'ordre 4 :

$$
\begin{cases}
a(0) = -1 \\
a(1) = 4 \\
a(2) = 176 \\
a(3) = 3136 \\
a(n) = -4 a(n-1) + 256 a(n-3) + 4096 a(n-4) & \text{pour } n \ge 4
\end{cases}
$$

La conjecture ouverte affirme que **tous les termes d'indice impair sont des carrés parfaits** :
```lean
/-- oeis_113254_conjecture_0: Conjecture: a(2*n+1) is a perfect square for all n. -/
theorem oeis_113254_conjecture_0 : ∀ n : ℕ, IsSquare (a (2 * n + 1)) := by
  sorry
```

---

## ⚡ 2. La Démonstration Mathématique Complète

### Étape 1 : Les Racines du Polynôme Caractéristique
L'équation caractéristique associée à la récurrence est :
$$P(X) = X^4 + 4X^3 - 256X - 4096 = 0$$

Ce polynôme se factorise exactement sous la forme :
$$P(X) = (X - 8)(X + 8)(X^2 + 4X + 64) = 0$$

Ses quatre racines sont :
* $r_1 = 8$
* $r_2 = -8$
* $r_3 = \alpha = -2 + 2i\sqrt{15}$
* $r_4 = \bar{\alpha} = -2 - 2i\sqrt{15}$

Remarquons que les quatre racines ont le **même module $|\cdot| = 8$**, en particulier :
$$|\alpha|^2 = \alpha \bar{\alpha} = (-2)^2 + (2\sqrt{15})^2 = 4 + 60 = \mathbf{64}$$

---

### Étape 2 : La Formule de Binet Explicite
D'après la théorie des suites récurrentes linéaires, $a(n)$ s'écrit :
$$a(n) = c_1 8^n + c_2 (-8)^n + c_3 \alpha^n + c_4 \bar{\alpha}^n$$

En résolvant le système linéaire imposé par les quatre conditions initiales $a(0) = -1, a(1) = 4, a(2) = 176, a(3) = 3136$, on obtient les coefficients exacts :
$$c_1 = 2, \quad c_2 = -2, \quad c_3 = \frac{\alpha}{4}, \quad c_4 = \frac{\bar{\alpha}}{4}$$

Ainsi, pour tout entier $n \ge 0$ :
$$a(n) = 2 \cdot 8^n - 2 (-8)^n + \frac{\alpha^{n+1} + \bar{\alpha}^{n+1}}{4}$$

---

### Étape 3 : Restriction aux Indices Impairs $n = 2m + 1$
Évaluons $a(2m + 1)$ :
1. Pour la partie réelle entière :
   $$2 \cdot 8^{2m+1} - 2 (-8)^{2m+1} = 2 \cdot 8^{2m+1} + 2 \cdot 8^{2m+1} = 4 \cdot 8^{2m+1} = 4 \cdot 8 \cdot 64^m = 32 \cdot 64^m = \frac{2 \cdot 64^{m+1}}{4}$$
2. En combinant avec les termes complexes :
   $$a(2m + 1) = \frac{2 \cdot 64^{m+1} + \alpha^{2m+2} + \bar{\alpha}^{2m+2}}{4}$$

Multiplions par $4$ :
$$4 a(2m + 1) = \alpha^{2m+2} + 2 \cdot 64^{m+1} + \bar{\alpha}^{2m+2}$$

---

### Étape 4 : L'Identité Remarquable Décisive
Puisque $\alpha \bar{\alpha} = 64$, on a :
$$64^{m+1} = (\alpha \bar{\alpha})^{m+1} = \alpha^{m+1} \bar{\alpha}^{m+1}$$

L'expression devient l'identité remarquable parfaite $A^2 + 2AB + B^2$ :
$$
\begin{aligned}
4 a(2m + 1) &= (\alpha^{m+1})^2 + 2 \, \alpha^{m+1} \bar{\alpha}^{m+1} + (\bar{\alpha}^{m+1})^2 \\
&= \mathbf{(\alpha^{m+1} + \bar{\alpha}^{m+1})^2}
\end{aligned}
$$

En divisant par $4 = 2^2$ :
$$
\mathbf{a(2m + 1) = \left( \frac{\alpha^{m+1} + \bar{\alpha}^{m+1}}{2} \right)^2}
$$

---

### Étape 5 : Intégrité des Racines Carrées
Posons :
$$b(m) = \frac{\alpha^{m+1} + \bar{\alpha}^{m+1}}{2} = \text{Re}(\alpha^{m+1})$$

Puisque $\alpha + \bar{\alpha} = -4$ et $\alpha \bar{\alpha} = 64$, la suite $b(m)$ satisfait la relation de récurrence entière du 2nd ordre :
$$
\begin{cases}
b(0) = \text{Re}(\alpha) = -2 \in \mathbb{Z} \\
b(1) = \text{Re}(\alpha^2) = -56 \in \mathbb{Z} \\
b(m) = -4 b(m-1) - 64 b(m-2) \in \mathbb{Z}
\end{cases}
$$

Par induction immédiate, **$b(m)$ est un entier relatif pour tout $m \in \mathbb{N}$**.  
Par conséquent :
$$a(2m + 1) = (b(m))^2 \quad \text{avec } b(m) \in \mathbb{Z}$$

**Tout terme d'indice impair $a(2m+1)$ est rigoureusement le carré d'un nombre entier.**  
**Q.E.D. (Ce qu'il fallait démontrer).** 🎯
