#lang scribble/manual
@require[@for-label[compiler2
                    @except-in[racket/base compile]]]

@title{compiler2}
@author{leif}

@defmodule[compiler2]

This is an unstable package for a variant of the Racket compiler written in
Racket using Nanopass.
It is not currently stable enough for most uses.

@defproc[(compiler [stx syntax?]) compilation-top?]{
The replacement compiler. Note that to use it, you must make sure to set
@racket[current-compile] to be this compiler.
}
