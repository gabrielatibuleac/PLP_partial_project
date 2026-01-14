inductive AExp where
|n: Int → AExp
|x: String → AExp
|adun : AExp → AExp → AExp
|scad : AExp → AExp → AExp
|inmul : AExp → AExp → AExp
|div : AExp → AExp → AExp
|mod : AExp → AExp → AExp
instance {n} : OfNat AExp n where
  ofNat := AExp.n (Int.ofNat n)

open AExp

infixl:65 " +' " => adun
infixl:65 " -' " => scad
infixl:70 " *' " => inmul
infixl:70 " /' " => div
infixl:70 " %' " => mod

inductive BExp where
|t : BExp
|f : BExp
|eq : AExp → AExp → BExp
|sm : AExp → AExp → BExp
|seq : AExp → AExp → BExp
|neg : BExp → BExp
|and : BExp → BExp → BExp
|or : BExp → BExp  → BExp
open BExp

infix:40 " =' " => eq
infix:40 " <' " => sm
infix:40 " <=' " => seq
prefix:35 "!' " => neg
infix:30 " &&' " => BExp.and
infix:30 " ||' " => BExp.or

inductive Com where
|skip : Com
|vardecl : String → AExp → Com
|assing : String → AExp → Com
|seq: Com → Com→ Com
|ite : BExp → Com → Com→ Com
|whilel : BExp → Com → Com
|forl : String → AExp → BExp → Com → Com
|block : Com → Com
|funf : String → List String → Com → Com
|func : String → List AExp → Com
open Com

notation:2 var " ::= " a => assing var a
notation:2 "var " v " := " a => vardecl v a
infixr:1 " ;; " => seq

def Env: Type := String → Int
def emptyEnv : Env := fun _ => 0

def update (σ : Env) (v : String) (val : Int) : Env :=
  fun x => if x == v then val else σ x
#check update

def FunEnv := String → Option (List String × Com )
def emptyFunEnv : FunEnv := fun _ => none

def updateFunEnv ( Γ : FunEnv ) (f : String) (p : List String ) (b : Com ) : FunEnv :=
    fun g => if g == f then some ( p, b) else Γ g

def stackl := List Env
def emptyS : stackl := []
def valueReturns := Option Int

inductive aeval : AExp → Env → Int → Prop where
|const : forall i σ ,
     aeval (n i ) σ i
|lookup : forall (v: String ) (σ : Env ),
     aeval (x v) σ (σ v)
|addd : forall a1 a2 i1 i2 σ ,
     aeval a1 σ i1 →
     aeval a2 σ i2 →
     aeval (a1 +' a2) σ (i1 + i2)
|sub : forall a1 a2 i1 i2 σ ,
    aeval a1 σ i1 →
    aeval a2 σ i2 →
    aeval (a1 -' a2 ) σ (i1 - i2)
|mul : forall a1 a2 i1 i2 σ ,
    aeval a1 σ i1 →
    aeval a2 σ i2 →
    aeval (a1 *' a2 ) σ (i1 * i2)
|dv :forall a1 a2 i1 i2 σ ,
  aeval a1 σ i1 →
  aeval a2 σ i2 →
  i2 ≠ 0→
  aeval (a1 /' a2 ) σ (i1 / i2)
|modulo :forall a1 a2 i1 i2 σ ,
  aeval a1 σ i1 →
  aeval a2 σ i2 →
  i2 ≠ 0→
  aeval (a1 %' a2 ) σ (i1 % i2)

notation: 50  "{ "e " , " σ " }=> " v => aeval e σ v
open aeval

inductive beval : BExp → Env → Bool -> Prop where
|boolt : forall σ ,
  beval t σ true
|boolf : forall σ ,
  beval f σ false
|beq : forall a1 a2 v1 v2 σ,
  aeval a1 σ v1 →
  aeval a2 σ v2 →
  beval ( a1 =' a2 ) σ (v1 = v2)
|blt : forall a1 a2 v1 v2 σ ,
  aeval a1 σ v1 →
  aeval a2 σ v2 →
  beval (a1 <' a2) σ (v1< v2)
|ble :forall a1 a2 v1 v2 σ ,
  aeval a1 σ v1 →
  aeval a2 σ v2 →
  beval (a1<=' a2 ) σ (v1 <= v2)
|bnotT : forall b σ ,
  beval b σ true →
  beval ( !' b ) σ false
|bnotF : forall b σ ,
  beval b σ false →
  beval ( !' b ) σ true
|bandT : forall b1 b2 σ ,
  beval b1 σ true →
  beval b2 σ true →
  beval (b1 &&' b2 ) σ true
|bandF1 : forall b1 b2 σ ,
  beval b1 σ false →
  beval ( b1 &&' b2 ) σ false
|bandF2 : forall b1 b2 σ ,
  beval b1 σ true →
  beval b2 σ false →
  beval ( b1 &&' b2 ) σ false
|borT1 : forall b1 b2 σ ,
   beval b1 σ true →
   beval (b1 ||' b2 ) σ true
|borT2 :forall b1 b2 σ ,
    beval b1 σ false →
    beval b2 σ true →
    beval (b1 ||' b2 ) σ true
|borF : forall b1 b2 σ ,
   beval b1 σ false →
   beval b2 σ false →
   beval (b1 ||' b2 ) σ false
notation:50 "{ " b " , " σ " }=> " v => beval b σ v
open beval

inductive evalargs :List AExp → Env → List Int → Prop where
|nil : forall σ ,
  evalargs [] σ []
|cons : forall a args σ v vals,
  aeval a σ v →
  evalargs args σ vals →
  evalargs (a :: args ) σ (v :: vals )

def params : Env → List String → List Int → Env
|σ , [], [] => σ
|σ , (p :: ps), (v :: vs) => params (update σ p v ) ps vs
|σ ,_, _ => σ

inductive eval : Com → Env → FunEnv → stackl → Env → FunEnv → stackl → valueReturns → Prop where
|bs_skip : forall σ Γ s,
  eval skip σ Γ s σ Γ s none
|bs_vardecl : forall v e σ Γ s i,
  aeval e σ i →
  eval (vardecl v e ) σ Γ s (update σ v i ) Γ s none
|bs_assing :forall v e σ Γ s i,
  aeval e σ i →
  eval (assing v e) σ Γ s (update σ v i ) Γ s none
|bs_seq : forall c1 c2 σ Γ s σ' Γ' s' r1 σ'' Γ'' s'' r2,
  eval c1 σ Γ s σ' Γ' s' r1 →
  eval c2 σ' Γ' s' σ'' Γ'' s'' r2 →
  eval (seq c1 c2 ) σ Γ s σ'' Γ'' s'' r2
|bs_iteT : forall b c1 c2 σ Γ s σ' Γ' s' r,
  beval b σ true →
  eval c1 σ Γ s σ' Γ' s' r →
  eval (Com.ite b c1 c2) σ Γ s σ' Γ' s' r
|bs_iteF : forall b c1 c2 σ Γ s σ' Γ' s' r,
  beval b σ false →
  eval c2 σ Γ s σ' Γ' s' r →
  eval (Com.ite b c1 c2) σ Γ s σ' Γ' s' r
|bs_whileF :forall b c σ Γ s,
  beval b σ false →
  eval (whilel b c) σ Γ s σ Γ s none
|bs_whileT : forall b c σ Γ s σ' Γ' s' r1 σ'' Γ'' s'' r2 ,
  beval b σ true →
  eval c σ Γ s σ' Γ' s' r1 →
  eval (whilel b c ) σ' Γ' s' σ'' Γ'' s'' r2→
  eval (whilel b c ) σ Γ s σ'' Γ'' s'' r2
|bs_forF :forall v a b c σ Γ s i1 ,
  aeval a σ i1 →
  beval b (update σ v i1) false →
  eval (forl v a b c ) σ Γ s (update σ v i1 ) Γ s none
|bs_forT :forall v a b c σ Γ s i1 σ' Γ' s' r1 σ'' Γ'' s'' r2,
  aeval a σ i1 →
  beval b (update σ v i1 ) true →
  eval c (update σ v i1 ) Γ s σ' Γ' s' r1 →
  eval (forl v a b c ) σ' Γ' s' σ'' Γ'' s'' r2 →
  eval (forl v a b c ) σ Γ s σ'' Γ'' s'' r2
|bs_block :forall c σ Γ s σ' Γ' s' r ,
  eval c σ Γ s σ' Γ' s' r→
  eval (block c) σ Γ s σ' Γ' s' r
|bs_funDecl :forall f param b σ Γ s,
  eval (funf f param b) σ Γ s σ (updateFunEnv Γ f param b ) s none
|bs_funCall : forall fn args σ Γ s param b argV σ1 σ' Γ' s1 r,
  Γ fn = some (param, b) →
  evalargs args σ argV →
  param.length =argV.length →
  σ1 = params emptyEnv param argV→
  eval b σ1 Γ (σ :: s) σ' Γ' s1 r →
  s1 = (σ :: s) →
  eval (func fn args) σ Γ s σ Γ' s r

notation:50 " { " c " , " σ ", " Γ ", " s "}⇓{ " σ' " , " Γ' " , " s' " , " r "}" =>
  eval c σ Γ s σ' Γ' s' r

def sigma0 :Env := emptyEnv
def sigma1 : Env :=  update emptyEnv "x" 5
def sigma2 : Env := update emptyEnv "x" 0
def sigma3 : Env :=  update (update (update emptyEnv "i" 0) "x" 5 ) "i" 0
def gama0 : FunEnv := updateFunEnv emptyFunEnv "f" ["x"] (vardecl "y" ((x "x") +' (n 1)))

theorem iff :
 { ite ((x "x") <' (n 3)) ("y" ::= (n 1)) ("y" ::= (n 2)) , sigma1 , emptyFunEnv , [] }⇓{ update sigma1 "y" 2 , emptyFunEnv , [] , none } := by
  apply eval.bs_iteF
  case a =>
    apply beval.blt (x "x") (n 3) 5 3 sigma1
    case a => apply aeval.lookup
    case a => apply aeval.const
  case a =>
    apply eval.bs_assing
    apply aeval.const

#check iff

theorem whilef :
{whilel ((x "x") <' (n 0)) ("x" ::= ((x "x") +' (n 1))), sigma1, emptyFunEnv, []}⇓{sigma1,emptyFunEnv,[],none} :=
by
  apply eval.bs_whileF
  apply beval.blt (x "x") (n 0) 5 0 sigma1
  case a => apply aeval.lookup
  case a => apply aeval.const

#check whilef

theorem forone :
{ forl "i" (n 0) ((x "x") <' (n 1)) ("x" ::= (n 5)),emptyEnv,emptyFunEnv,[]}⇓{sigma3,emptyFunEnv,[],none}:=
by
  apply eval.bs_forT
  case a =>
    apply aeval.const
  case a =>
    apply beval.blt (x "x") (n 1) 0 1 (update emptyEnv "i" 0)
    case a => apply aeval.lookup
    case a => apply aeval.const
  case a =>
    apply eval.bs_assing
    apply aeval.const
  case a =>
    apply eval.bs_forF
    case a =>
      apply aeval.const
    case a =>
      apply beval.blt (x "x") (n 1) 5 1 (update (update (update emptyEnv "i" 0) "x" 5) "i" 0)
      case a => apply aeval.lookup
      case a => apply aeval.const
#check forone

def g1 : FunEnv := updateFunEnv emptyFunEnv "f" ["x"] (vardecl "y" ((x "x") +' (n 1)))

theorem function1 :
  { (funf "f" ["x"] (vardecl "y" ((x "x") +' (n 1)))) ;; (func "f" [n 5]), emptyEnv, emptyFunEnv, [] }⇓{ emptyEnv, g1, [], none } := by
  apply eval.bs_seq (σ' := emptyEnv) (Γ' := g1) (s' := []) (r1 := none)
  case a =>
    apply eval.bs_funDecl
  case a =>
    apply eval.bs_funCall
      (param := ["x"])
      (b := vardecl "y" ((x "x") +' (n 1)))
      (argV := [5])
      (σ1 := update emptyEnv "x" 5)
      (σ' := update (update emptyEnv "x" 5) "y" 6)
      (s1 := [emptyEnv])
    · rfl
    · apply evalargs.cons
      · apply aeval.const
      · apply evalargs.nil
    · rfl
    · rfl
    · apply eval.bs_vardecl
      apply aeval.addd (x "x") (n 1) 5 1 (update emptyEnv "x" 5)
      · apply aeval.lookup
      · apply aeval.const
    · rfl

#check function1
