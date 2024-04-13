# Lean

Lean это система интерактивного доказательства теорем, основанная на исчислении индуктивных построений. Она станет нашим основным инструментом.

## Установка

Для работы с Lean нам потребуются система управления версиями [Git](https://git-scm.com/downloads) и редактор исходного кода [Visual Studio Code](https://code.visualstudio.com/download).

Ставим сначала Git, затем VS Code. После чего, открываем VS Code, переходим на вкладку расширений и ищем расширение `lean4`:

![](../prose/_img/code-ext.png)

Устанавливаем это расширение. Теперь осталось лишь открыть проект.

Используем Git, чтобы скачать заготовку проекта:

- Нажимаем клавишу F1 в VS Code
- Пишем `git clone` и нажимаем Enter
- Вставляем следующий URL и нажимаем Enter: `https://github.com/suhr/polygon.git`

После выбора директории, VS Code скачает проект и предложит открыть его.

В меню VS Code выбираем `View > Explorer` и щёлкаем в панели слева на файл `Basics.lean`, чтобы открыть его.

## Основы Lean

```lean
def name: type := expr
```

```lean
example: type := expr
```

- `λx:τ => e`, `fun x:τ => β`
- `e1 e2`
- `∀x:α, β`, `(x: α) → β`
- `let x := v;  e`

```
Sort 0 : Sort 1 : ...
```

```
Prop : Type 0 : Type 1 : Type 2 : ...
```


casesOn

```
And.intro : ∀{a b: Prop}, a → b → a ∧ b
And.left  : ∀{a b: Prop}, a ∧ b → a
And.right : ∀{a b: Prop}, a ∧ b → b

Or.inl  : ∀{a b: Prop}, a → a ∨ b
Or.inr  : ∀{a b: Prop}, b → a ∨ b
Or.elim : ∀{a b c: Prop}, a ∨ b → (a → c) → (b → c) → c

False.elim : False → C
```

```lean
example {P Q: Prop}(pq: P ∨ Q)(np: ¬P): Q :=
  _
```

Выражение `_` называется *дыркой*. Lean не может придумать доказательство на место дырки, но зато он показывает нам её тип, вместе с контекстом:

```
Expected type
PQ: Prop
pq: P ∨ Q
np: ¬P
⊢ Q
```

Напишем часть доказательства:

```lean
example {P Q: Prop}(pq: P ∨ Q)(np: ¬P): Q :=
  pq.elim _ _
```

Lean показывает, что одна из дырок имеет тип `P → Q`, а другая — `Q → Q`.

Допишем ещё:

```lean
example {P Q: Prop}(pq: P ∨ Q)(np: ¬P): Q :=
  pq.elim (λp => _) (λq => _)
```

Контексты у дырок становятся разными: в одном `p : P`, а в другом `q : Q`.

Наконец, запишем доказательство полностью:

```lean
example {P Q: Prop}(pq: P ∨ Q)(np: ¬P): Q :=
  pq.elim (λp => (np p).elim) (λq => q)
```

Важно уметь сопоставить выражение с рассуждением по шагам. Выражение выше соответствует следующему рассуждению:

1. Рассмотрим $P ∨ Q$
2. Пусть $P$
    1. Но это невозможно, так как $¬P$
3. Пусть $Q$
    1. Тогда $Q$

Другой пример: докажем, что $P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)$:

```lean
example {P Q R: Prop}(pqr: P ∧ (Q ∨ R)): (P ∧ Q) ∨ (P ∧ R) :=
  let ⟨p,qr⟩ := pqr;  qr.elim (λq => Or.inl ⟨p,q⟩) (λr => Or.inr ⟨p,r⟩)
```

Выражение `let` позволяет не только вводить локальные определения, но и разбирать доказательства выражений вида $P ∧ Q$ на части.

Доказательству выше соответствует рассуждение

1. Из $P ∧ (Q ∨ R)$ следуют $P$ и $Q ∨ R$
2. Рассмотрим $Q ∨ R$
    1. Пусть $Q$. Тогда $P ∧ Q$ и, следовательно, $(P ∧ Q) ∨ (P ∧ R)$
    2. Пусть $R$. Тогда $P ∧ R$ и отсюда $(P ∧ Q) ∨ (P ∧ R)$

Третий пример:

```lean
example {P Q: Prop}(pq: P → Q)(nq: ¬Q): ¬P :=
  λp => nq (pq p : Q)
```

Соответствующее рассуждение:

1. Предположим, что $P$
    1. Так как $P → Q$, то $Q$
    2. Что абсурдно, так как $¬Q$
2. Следовательно, $¬P$


Теперь упражнения. Простые:

```lean
example {P Q: Prop}(pq: P ∧ Q): Q ∧ P := _
example {P Q R: Prop}(pQr: P ∧ (Q ∧ R)): (P ∧ Q) ∧ R := _
example {P Q: Prop}(p: P): Q → P := _
example {P Q R: Prop}(pqr: P → Q → R): P ∧ Q → R := _
example {P Q R: Prop}(pqr: P → Q → R)(pq: P → Q): P → R := _
example {P Q R: Prop}(pq: P → Q)(qr: Q → R): P → R := _
example {P Q: Prop}(npq: ¬(P ∨ Q)): ¬P ∧ ¬Q := _
example {P Q: Prop}(npQ: ¬P ∨ Q): P → Q := _
example {P Q R: Prop}(pQr: P → Q ∧ R): (P → Q) ∧ (P → R) := _
example {P Q R: Prop}(pqR: P ∨ Q → R): (P → R) ∧ (Q → R) := _
```

Сложнее:

```lean
example {P Q R: Prop}(pqR: (P ∨ Q) ∨ R): P ∨ (Q ∨ R) := _
example {P Q R: Prop}(pqPr : (P ∧ Q) ∨ (P ∧ R)): P ∧ (Q ∨ R) := _
example {P Q R: Prop}(pQr: P ∨ (Q ∧ R)): (P ∨ Q) ∧ (P ∨ R) := _
```

Не обязательно решать их все, но необходимо понимать, как каждое из них может быть решено. К каждому решению следует привести рассуждение.

Упражнения на $∀$ и $∃$ выделены в отдельный блок. Но сначала примеры.

Докажем, что $(∀x.\; P\ x ∧ Q\ x) → (∀x.\; P\ x) ∧ (∀x.\; Q\ x)$:

```lean
example {P Q: α → Prop}(apq: ∀x, P x ∧ Q x): (∀x, P x) ∧ (∀x, Q x) :=
  ⟨λx => (apq x).left,  λx => (apq x).right⟩
```

Рассуждение:

1. Пусть $x:τ$
    1. Тогда $P\ x ∧ Q\ x$
    2. Отсюда $P\ x$
2. Следовательно, $∀x.\; P\ x$
3. Пусть $x$ это значение типа $τ$
    1. Тогда $P\ x ∧ Q\ x$
    2. Отсюда $Q\ x$
4. Следовательно, $∀x.\; Q\ x$
5. Отсюда $(∀x.\; P\ x) ∧ (∀x.\; Q\ x)$

Другой пример:

```lean
example {P: α → β → Prop}(eap: ∃x, ∀y, P x y): ∀y, ∃x, P x y :=
  let ⟨x,ap⟩ := eap;  λy => ⟨x, (ap y : P x y)⟩
```

`let` позволяет разобрать и $∃x:τ.\; P\ x$ на $x:τ$ и $P\ x$.

Рассуждение:

1. Возьмём такое $x$, что $∀y.\; P\ x\ y$
2. Покажем, что $∀y, ∃x, P\ x\ y$
    1. Пусть дано некоторое значение $y$
    2. Тогда $P\ x\ y$
    3. Следовательно, $∃x.\; P\ x\ y$

Ещё раз, правила для $∃$:

```
Exists.intro : ∀{α: Sort u}{p: α → Prop},
  (w:α) → p w → Exists p
Exists.elim : ∀{α: Sort u}{p: α → Prop}{b : Prop},
  (∃x, p x) → (∀(a:α), p a → b) → b
```

И упражнения. Простые:

```lean
example {P: α → β → Prop}(ap: ∀x, ∀y, P x y): ∀y, ∀x, P x y := _
example {P: α → β → Prop}(ep: ∃x, ∃y, P x y): ∃y, ∃x, P x y := _
example {P: α → Prop}(ne: ¬∃x, P x): ∀x, ¬(P x) := _
example {P: α → Prop}{Q: Prop}(epQ: (∃x, P x) → Q): ∀x, P x → Q := _
example {P: α → Prop}{Q: Prop}(apq: ∀x, P x → Q): (∃x, P x) → Q := _
```

Сложнее:

```lean
example {P Q: α → Prop}(aa: (∀x, P x) ∨ (∀x, Q x)): ∀x, P x ∨ Q x := _
example {P Q: α → Prop}(ee: (∃x, P x) ∨ (∃x, Q x)): ∃x, P x ∨ Q x := _
```
