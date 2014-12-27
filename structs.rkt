#lang typed/racket/base

(provide (all-defined-out))

(struct topform () #:transparent)

(struct topgenform topform ([body : genform])
        #:transparent)

(struct topexpr topform ([body : expression])
        #:transparent)

(struct topmod topform ([id : Identifier]
                        [path : Module-Path]
                        [body : (Listof modform)])
        #:transparent)

(struct topbeg topform ([body : (Listof topform)])
        #:transparent)

(struct topbegfs topform ([body : (Listof topform)])
        #:transparent)

(struct modform () #:transparent)

(struct modgenform modform ([body : genform])
        #:transparent)

(struct pro modform ([spec : (Listof Any)]) ;; TODO
        #:transparent)

(struct modbegfs modform ([body : (Listof modform)])
        #:transparent)

(struct decl modform ([body : (Listof Any)]) ;; TODO
        #:transparent)

(struct submodform modform () #:transparent)

(struct submod submodform ([id : Identifier]
                    [path : Module-Path]
                    [body : (Listof modform)])
        #:transparent)

(struct submod* submodform ([id : Identifier]
                     [path : (U Module-Path #f)]
                     [body : (Listof modform)])
        #:transparent)

(struct genform () #:transparent)

(struct defv genform ([id : (Listof Identifier)]
                      [body : expression])
        #:transparent)

(struct defsyntaxs defv () #:transparent)

(struct req genform ([spec : (Listof Any)]) ;; TODO
        #:transparent)

(struct expression genform () #:transparent)

(struct ide expression ([id : Identifier])
        #:transparent)

(struct lam expression ([args : (Listof Identifier)]
                        [rest : (U Identifier #f)]
                        [body : (Listof expression)])
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

(struct setv expression ([id : Identifier]
                         [body : expression])
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

(struct top expression ([id : Identifier])
        #:transparent)

(struct varref ([id : (U top Identifier #f)])
        #:transparent)

