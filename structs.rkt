#lang typed/racket/base

(provide (all-defined-out))

(struct topform () #:transparent)

(struct topgenform topform ([body : genform])
        #:transparent)

(struct topexp topform ([body : expr])
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

(struct begfs modform ([body : (Listof modform)])
        #:transparent)

(struct decl modform ([body : (Listof Any)]) ;; TODO
        #:transparent)

(struct submod modform () #:transparent)

(struct mod submod ([id : Identifier]
                    [path : Module-Path]
                    [body : modform])
        #:transparent)

(struct mod* submod ([id : Identifier]
                     [path : (U Module-Path #f)]
                     [body : modform])
        #:transparent)

(struct genform () #:transparent)

(struct defvals genform ([id : (Listof Identifier)]
                 [body : expr])
        #:transparent)

(struct defsyntaxs genform ([id : (Listof Identifier)]
                    [body : expr])
        #:transparent)

(struct req genform ([spec : (Listof Any)]) ;; TODO
        #:transparent)

(struct expr genform () #:transparent)

(struct lam expr ([args : (Listof Identifier)]
                  [rest : (U Identifier #f)]
                  [body : expr])
        #:transparent)

(struct caselam expr ([lams : (Listof lam)])
        #:transparent)

(struct branch expr ([condition : expr]
                     [consequent : expr]
                     [alternative : expr])
        #:transparent)

(struct beg expr ([body : (Listof expr)])
        #:transparent)

(struct beg0 expr ([body : (Listof expr)])
        #:transparent)

(struct letv expr ([id : (Listof Identifier)]
                   [val : expr]
                   [body : expr])
        #:transparent)

(struct letrecv letv () #:transparent)

(struct setv expr ([id : Identifier]
                   [body : expr])
        #:transparent)

(struct quo expr ([datum : Any])
        #:transparent)

(struct quosyntax expr ([datum : Any])
        #:transparent)

(struct withcm expr ([key : expr]
                     [val : expr]
                     [result : expr])
        #:transparent)

(struct app expr ([f : expr]
                  [args : (Listof expr)])
        #:transparent)

(struct top expr ([id : Identifier])
        #:transparent)

(struct varref ([id : (U top Identifier #f)])
        #:transparent)

