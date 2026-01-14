# PLP_partial_project

Temă - evaluare pe parcurs
Considerăm un limbaj imperativ cu funcții, blocuri și declarații de variabile, a cărui sintaxă este definită după cum urmează:

Expresii aritmetice (AExp):

a ::= n                   (constante întregi)
    | x                   (variabile)
    | a₁ + a₂             (adunare)
    | a₁ - a₂             (scădere)
    | a₁ * a₂             (înmulțire)
    | a₁ / a₂             (împărțire)
    | a₁ % a₂             (modulo)
Expresii booleene (BExp):

b ::= true                (constanta adevărat)
    | false               (constanta fals)
    | a₁ = a₂             (egalitate)
    | a₁ < a₂             (mai mic)
    | a₁ ≤ a₂             (mai mic sau egal)
    | ¬b                  (negație)
    | b₁ ∧ b₂             (conjuncție)
    | b₁ ∨ b₂             (disjuncție)
Comenzi (Com):

c ::= skip                          (comanda vidă)
    | var x := a                    (declarație de variabilă cu inițializare)
    | x := a                        (atribuire)
    | c₁; c₂                        (secvență de comenzi)
    | if b then c₁ else c₂          (condițională)
    | for x := a₁; b do c           (buclă for)
    | { c }                         (bloc - creează domeniu de vizibilate nou)
    | fun f(x₁,...,xₙ) { c }        (declarație de funcție)
    | f(a₁,...,aₙ)                  (apel de funcție)
Cerințe
Cerința principală a temei este să definiți semantica operațională pentru limbajul de mai sus. Desigur, implementarea necesită și codificarea sintaxei de mai sus, care va avea punctaj propriu.

Tema are două livrabile:
O documentație scrisă. Aceasta o puteți scrie de mână sau într-un editor de texte, dar e important ca la final să obțineți un PDF.
Implementarea. Aceasta trebuie să fie în Lean.
Pentru primul livrabil (documentația scrisă), trebuie detaliate următoarele aspecte:

a) Definiția configurației - Precizați forma configurațiilor pentru limbajul de mai sus.

Indicii: - veți avea nevoie de o componentă în care să păstrați codul ce trebuie executat. - veți avea nevoie de σ (stare): funcție parțială Var → ℤ pentru valorile variabilelor - veți avea nevoie de Γ (environment funcții): funcție parțială FunName → (Params, Body) pentru păstrarea funcțiilor - veți avea nevoie de o componentă pentru stocarea valorilor returnate de funcții - veți avea nevoie de o stivă pentru a salva stările înainte de apelurile de funcții și pentru recupera stările la terminarea execuției funcțiilor

Important: configurația poate fi un tuplu cu toate componentele pe care le considerați necesare. Atenție la partea de declarații de variabile și la domeniul de vizibilitate al acestora. Este important să aveți o înțelegere clară a mecanismului de gestionare al variabilelor în contextul domeniilor de vizibilitate și să-l explicați corespunzător în document.

b) Regulile semanticii

Scrieți reguli (sub forma de reguli de inferență) pentru fiecare construcție a limbajului de mai sus. Se vor puncta doar regulile scrise corect (adică au un nume, premizele și concluzia sunt relații între configurații, condițiile sunt scrise corect și cu sens).

c) Exemple de derivări

Prezentați cel puțin un arbore de derivare pentru un program netrivial (adică să nu fie doar skip sau doar o atribuire). Deoarece este destul de dificil să scriem derivări de mână, veți scrie doar o singură derivare în documentația scrisă, restul pot fi doar în implementare.

Barem
Implementarea trebuie să reflecte întocmai definițiile din documentația scrisă. Tema va fi evaluată parcurgând întâi documentația și apoi verificând că implementarea este conformă și funcționează așa cum este indicat. Punctajele se acordă astfel:

Definiția configurației - 5p: 3p descrierea configurației în documentație și 2p implementarea conform cu descrierea scrisă;

Regulile semanticii - 20p: 10p descrierea regulilor în documentație (3p - regulile pentru expresiile aritmetice, 2p pentru expresiile boolene, 5p pentru regulile corespunzătoare instrucțiunilor) și 10p pentru implementarea regulilor (punctate similarȘ 3p+2p+5p).

Exemple de derivări care să acopere toate regulile semanticii - 15p: 3p pentru o derivare în documentația scrisă; 12p pentru derivările din implementare.

