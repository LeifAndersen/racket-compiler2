#lang typed/racket/base/no-check

(provide (all-defined-out))

(struct topform () #:transparent)

#|
Input Lang :
<top-level-form> ::= <general-top-level>
                  |  (#%expression <expr>)
                  |  (module <id> <module-path>
                       (#%plain-module-begin <module-top-level-form>))
                  |  (begin <to-level-form> ...)
                  |  <begin-for-syntax <top-level-form> ...)

<module-level-form> ::= <general-top-level>
                     |  (#%provide <raw-provide-spec>)
                     |  (begin-for-syntax <module-level-form>)
                     |  <submod-form>
                     |  (#%declare <declaration-keys> ...)

<submodule-form> ::= (module <id> <module-path>
                       (#%plain-module-begin <module-level-form> ...))
                  |  (module* <id> <module-path
                       (#%plain-module-begin <module-level-form> ...))
                  |  (module* <id> #f
                       (#%plain-module-begin <module-level-form> ...))

<general-top-level-form> ::= <expr>
                          |  (define-values (<id> ...) <expr>)
                          |  (define-syntaxes (<id> ...) <expr>)
                          |  (#%require <raw-require-spec> ...)

<expr> ::= <id>
        |  (#%plain-lambda <formals> <expr> ...+)
        |  (case-lambda (<formals> <expr> ...+) ...)
        |  (if <expr> <expr> <expr>)
        |  (begin <expr> ...)
        |  (begin0 <expr> ...)
        |  (let-values ([(<id> ...) <expr>] ...) <expr> ...+)
        |  (letrec-values ([(<id> ...) <expr>] ...) <expr> ...+)
        |  (set! <id> <expr>)
        |  (quote <datum>)
        |  (quote-syntax <datum>)
        |  (with-continuation-mark <expr> <expr> <expr>)
        |  (#%plain-app <expr> ...+)
        |  (#%top . <id>)
        |  (#%variable-reference <id>)
        |  (#%variable-reference (#%top . <id>))
        |  (#%variable-reference)

<formals> ::= (<id> ...)
           |  (<id> ... . <id>)
           |  <id>

Pass 1: Let/Letrec
...
<expr> ::=
-       |  (#%plain-lambda <formals> <expr> ...+)
+       |  <lam>

-       |  (let-values ([(<id> ...) <expr>] ...) <expr> ...+)
+       |  (let ([<id> <expr>] ...) <expr> ...+)

-       |  (letrec-values ([(<id> ...) <expr>] ...) <expr> ...+)
+       |  (letrec-lam ([<id> <lam>] ...) <expr> ...+)
+       |  (let-void (<id> ...) <expr> ...+)

-       |  (set! <id> <expr>)
+       |  (set!-values (<id> ...) <expr>)

<lam> ::= (#%plain-lambda <formals> <expr> ...+)
...

Pass 2: Determine Mutable Variables
Pass 3: Mutable Variable Elimination
...
<expr> ::=
-       |  (set!-values (<id> ...) <expr>)
+       |  (set!-boxes (<id> ...) <expr>)
+       |  (box! <id>)
+       |  (unbox <id>)
-       |  (let ([<id> <expr>] ...) <expr> ...+)
+       |  (let ([<bid> <expr>] ...) <expr> ...+)
-       |  (let-void (<id> ...) <expr> ...+)
+       |  (let-void (<bid> ...) <expr> ...+)
...

Pass 3: Closure Conversion
...
<expr> ::=
+        |  (proc-const <id> <expr>)

<lam> ::=
-       |  (#%plain-lambda <formals> <expr> ...+)
+       |  (#%plain-lambda <formals> ((<id> <type>) ...) <expr> ...+)

<formals> ::=
-          |  (<id> ...)
+          | ((<id> <type> ...)
-          |  (<id> ... . <id>)
+          |  ((<id> <type> ... . (<id> <type>))
-          |  <id>
+          |  (<id> <type>)
...

Pass 4: Inlining
???

Pass 5: De Bruijn Indices
...
<general-top-level-form> ::= <expr>
                          |  (define-values (<dbid> ...) <expr>)
                          |  (define-syntaxes (<dbid> ...) <expr>)
                          |  (#%require <raw-require-spec> ...)

<expr> ::=
-       |  <id>
+       |  <dbid>
-       |  (let ([<id> <expr>] ...) <expr> ...+)
+       |  (let ([<dbid> <expr>] ...) <expr> ...+)
-       |  (letrec-lam ([<id> <lam>] ...) <expr> ...+)
+       |  (letrec-lam ([<dbid> <lam>] ...) <expr> ...+)
-       |  (let-void (<id> ...) <expr> ...+)
+       |  (let-void (<dbid> ...) <expr> ...+)
-       |  (#%top . <id>)
+       |  (#%top . <dbid>)
-       |  (#%variable-reference <id>)
+       |  (#%variable-reference <dbid>)
-       |  (#%variable-reference (#%top . <id>))
+       |  (#%variable-reference (#%top . <dbid>))

<formals> ::=
-          |  ((<id> <type>) ...)
+          |  ((<dbid> <type>) ...)
-          |  ((<id> <type>) ... . (<id> <type>))
+          |  ((<dbid> <type>) ... . (<dbid> <type>))
-          |  (<id> <type>)
+          |  (<dbid> <type>)

|#


(struct topgenform topform ([body : genform])
        #:transparent)

(struct topexpr topform ([body : expression])
        #:transparent)

(struct topmod topform ([id : ide]
                        [path : Module-Path]
                        [body : (Listof modform)])
        #:transparent)

(struct topbeg topform ([body : (Listof topform)])
        #:transparent)

(struct topbegfs topform ([body : (Listof topform)])
        #:transparent)

(struct modform topform () #:transparent)

(struct modgenform modform ([body : genform])
        #:transparent)

(struct pro modform ([spec : (Listof Any)]) ;; TODO
        #:transparent)

(struct modbegfs modform ([body : (Listof modform)])
        #:transparent)

(struct decl modform ([body : (Listof Any)]) ;; TODO
        #:transparent)

(struct submodform modform () #:transparent)

(struct submod submodform ([id : ide]
                           [path : Module-Path]
                           [body : (Listof modform)])
        #:transparent)

(struct submod* submodform ([id : ide]
                            [path : (U Module-Path #f)]
                            [body : (Listof modform)])
        #:transparent)

(struct genform () #:transparent)

(struct defv genform ([id : (Listof ide)]
                      [body : expression])
        #:transparent)

(struct defsyntaxs defv () #:transparent)

(struct defv1 genform ([id : (U ide var)]
                       [body : expression])
        #:transparent)

(struct deflam genform ([id : (U ide var)]
                        [body : lam])
        #:transparent)

(struct req genform ([spec : (Listof Any)]) ;; TODO
        #:transparent)

(struct expression genform () #:transparent)

(struct ide expression ([id : Symbol]
                        [val : Identifier])
        #:transparent)

(struct voi expression ()
        #:transparent)

(struct var expression ([id : ide]
                        [type : (U 'val 'ref 'flonum 'fixnum 'extflonum)])
        #:transparent)

(struct lam expression ([args : (Listof ide)]
                        [rest : (U ide #f)]
                        [body : expression])
        #:transparent)

(struct caselam expression ([lams : (Listof lam)])
        #:transparent)

(struct branch expression ([test : expression]
                           [tbranch : expression]
                           [fbranch : expression])
        #:transparent)

(struct beg expression ([body : (Listof expression)])
        #:transparent)

(struct beg0 expression ([body : (Listof expression)])
        #:transparent)

(struct letv expression ([defs : (Listof defv)]
                         [body : expression])
        #:transparent)

(struct letrecv letv () #:transparent)

(struct letv1 expression ([defs : (Listof defv1)]
                          [body : expression])
        #:transparent)

(struct letreclam expression ([defs : (Listof deflam)]
                              [body : expression])
        #:transparent)

(struct letvoid expression ([defs : (Listof ide)]
                            [body : expression])
        #:transparent)

(struct setv expression ([id : (Listof ide)]
                         [body : expression])
        #:transparent)

(struct setb expression ([id : (Listof ide)]
                         [body : expression])
        #:transparent)

(struct bo expression ([id : ide])
        #:transparent)

(struct unbo expression ([id : ide])
        #:transparent)

(struct quo expression ([datum : Any])
        #:transparent)

(struct quosyntax expression ([datum : Any])
        #:transparent)

(struct withcm expression ([key : expression]
                           [val : expression]
                           [result : expression])
        #:transparent)

(struct app expression ([f : expression]
                        [args : (Listof expression)])
        #:transparent)

(struct top expression ([id : ide])
        #:transparent)

(struct varref ([id : (U top ide #f)])
        #:transparent)
