Uniwersum Definicyjnie Rozstrzygalnych Zdań

Motywacja:
1. Początkujących zawsze myli różnica między Bool i Prop.
2. W sumie filozoficznie to typ Bool wydaje się być fundamentalny, więc dziwne, że nie jest wbudowany, tylko induktywny.
3. Nawet jeśli mamy uniwersum zdań definicyjnie irrelewantnych i klasycznych, to niektóre z nich i tak mają zawartość obliczeniową, a inne nie.
4. Zdania rozstrzygalne stanowią bardzo podstawowe pojęcie, które powinno pojawić się w każdej bibliotece standardowej, ale instancje generują masę bojlerplejtu.
5. Konwersja między zdaniem i jego funkcją rozstrzygającą też generuje masę bojlerplejtu, vide ssreflect. Może ssreflect powinien być wbudowany w język?

Rozwiązanie:

Wprowadzamy uniwersum zdań, które są "definicyjnie" rozstrzygalne, tzn. śledzimy rozstrzygalność na poziomie systemu typów. Nazwijmy je Dec.

`Dec` żyje w `Type 0`

```
Dec : Type 0
```

Podstawowe zdania zamieszkujące to uniwersum to `True` i `False` (ale to nie wszystko, bo będą też inne.)

```
True : Dec
False : Dec
```

Wyposażamy uniwersum `Dec` w eliminator (który pewnie powinien być zależny, ale na razie się tym nie przejmujmy). 

```
if : forall A : Type. Dec -> A -> A -> A
```

Eliminator liczy tak jak zwykły `if` dla typu `Bool` (obliczanie będę oznaczał za pomocą `→`):

```
if True x y → x
if False x y → y
```

Reguły unikalności są banalne

```
True ≡ True
False ≡ False
```

W naszym systemie będziemy też mieli uniwersum zdań `Prop`, które jest irrelewantne. Podstawowe spójniki logiczne (`~`, `/\`, `\/`, `->`) są przeładowane: jeśli argumenty są w `Dec`, to całość też. Jeżeli któryś argument jest w `Prop`, to całość jest w `Prop`. Kwantyfikatory `forall` i `exists` są zawsze w `Prop`.

Poza podstawowymi regułami obliczania i unikalności są też dodatkowe reguły odpowiadające tabelkom prawdy, o których jeszcze nie wiem, czy powinny być regułami obliczania czy unikalności. Wydaje mi się, że jeżeli zdanie jest argumentem `if`a, to powinno się obliczać, a jeśli nie, to nie powinno.

```
~ True ≡ False
~ False ≡ True

True /\ True ≡ True
False /\ _ ≡ False
_ /\ False ≡ False

True \/ _ ≡ True
_ \/ True ≡ True
False \/ False ≡ False

False -> _ ≡ True
_ -> True ≡ True
```

No i kluczowy moment. Między `Dec` i `Prop` zachodzi kumulatywność/podtypowanie. Jak tylko zdanie trafi do `Prop`, to traci powyższe nadzwyczajne moce obliczeniowe. Dodatkowo jeśli zdanie z `Dec` jest prawdziwe, to możemy wygenerować dowód tego zdania w Prop, a jeśli jest fałszywe, to dowód jego zaprzeczenia (`fromDec`, `proof` i `contra` zapewne powinny być implicitne, ale będę je pisał, żeby się nie pogubić).


```
P : Dec
----------------
fromDec P : Prop
```

```
P : Dec     P ≡ True
--------------------
proof P : fromDec P
```

```
P : Dec     P ≡ False
---------------------
contra : fromDec (~ P)
```

Przykładowe obliczenia: mamy `True -> True /\ True ≡ True`. Jeśli chodzi o typ, to `fromDec (True -> True /\ True)` oblicza się do `True -> True /\ True`. Wobec tego

```
proof (True -> True /\ True)
→
fun _ => /\-intro * *
```

No i teraz jeszcze kluczowszy moment: w `Dec` nie wolno definiować typów induktywnych, ale wolno definiować predykaty i relacje przez rekursję po argumentach. Te definicje `fromDec` automatycznie przerabia na definicje induktywne w `Prop`. W takich definicjach pattern matching nie musi być zupełny (pominięte przypadki obliczają się do `False`), a po prawej stronie zamiast `True` piszemy nazwę, która będzie służyć jako nazwa definiującego równania (w `Dec`) lub nazwa konstruktora (w `Prop`), potencjalnie z argumentami.

Przykład (składnia z dupy):

```
rec isEven (n : Nat) : Dec :=
match n with
| 0 => Even0
| S (S n') => EvenSS (isEven n')
```

Na Coqowe odpowiada to następującej funkcji i predykatowi oraz dowodowi, że ta funkcja rozstrzyga ten predykat.

```Coq
Fixpoint isEven (n : nat) : bool :=
match n with
| 0 => true
| 1 => false
| S (S n') => isEven n'
end.

Inductive Even : nat -> Prop :=
| Even0 : Even 0
| EvenSS : forall {n : nat}, Even n -> Even (S (S n)).

Lemma isEven_spec :
  forall (n : nat), reflect (Even n) (isEven n).
```

Za pomocą rekurencyjnej definicji zdania w `Dec` możemy zarówno liczyć, np. `isEven 4 → True`, `isEven 5 → False`, jak i dowodzić, np. `EvenSS (EvenSS Even0) : fromProp (isEven 4)`, `fun e => match e with end : fromProp (isEven 5) -> False`. Oczywiście możemy też dowodzić równań w `Dec` za pomocą przepisywania.

Wydaje się, że już jest zajebiście, ale to jeszcze nie koniec. Załóżmy teraz, że pracujemy w Obserwacyjnej Teorii Typów. Okazuje się, że dostajemy za darmo (w pewnym sensie) potężne benefity: jeżeli dany typ ma rozstrzygalną równość, to możemy automatycznie wrzucić ją do `Dec`. Po stronie obliczeniowej korzystamy z reguł obliczania dla równości dla tego typu, a po stronie zdaniowej zostawiamy po prostu sam typ równości.

Przykład: dla równości na `Nat` mamy w systemie reguły `0 = 0 ≡ True`, `0 = S _ ≡ False`, `S _ = 0 ≡ False`, `S n = S m ≡ n = m`, z których jesteśmy w stanie wygenerować rozstrzygacz dla równości. Dla jasności nazwijmy go `nat_eq_dec : Nat -> Nat -> Dec` (chociaż docelowo oczywiście będziemy go zapisywać po prostu jako `n = m : Dec`). W `Prop` mamy za to `fromDec (nat_eq_dec n m) → n = m`.

Reguły sortowania dla równości są raczej proste: równość na pustym, unicie, produktach, sumach i sumach zależnych ląduje w `Dec` (pod warunkiem, że argumenty to typy, których równość też jest w `Dec`). Równość na zdaniach z `Dec` też ląduje w `Dec`. Z drugiej strony, równość na funkcjach, typach i zdaniach z `Prop` ląduje w `Prop`.

Jeżeli mamy w języku mechanizm definiowania typów induktywnych, który dba o generowanie odpowiednich reguł obliczania dla typu równości, to możemy dość łatwo zmodyfikować go, żeby umieszczał równość w `Dec`, jeśli jest rozstrzygalna. Wystarczy jakoś tam śledzić, czy argumenty konstruktorów też mają rozstrzygalną równość.

No i voilà! Mamy uniwersum definicyjnie rozstrzygalnych zdań (w sumie to nawet nie jest uniwersum, tylko zwykły typ, bo nie potrzeba nam prooftermów w `Dec`). Dzięki `Dec` nie trzeba się ciągle przełączać między `Prop` i `Bool` (ssreflect wbudowany w język), a przynajmniej nie zawsze - wiadomo, że żeby udowodnić rozstrzygalność niektórych zdań, i tak trzeba się będzie narobić. W Obserwacyjnej Teorii Typów dostajemy też dodatkowo darmowy deriving dla rozstrzygalnej równości.