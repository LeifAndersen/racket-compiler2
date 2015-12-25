compiler2
=========
Current status of a new racket compiler that uses [Nanopass][1]

[![Build Status](https://travis-ci.org/LeifAndersen/racket-compiler2.svg?branch=master)](https://travis-ci.org/LeifAndersen/racket-compiler2)
[![Coverage Status](https://coveralls.io/repos/LeifAndersen/racket-compiler2/badge.svg?branch=master&service=github)](https://coveralls.io/github/LeifAndersen/racket-compiler2?branch=master)

# Features of Racket currently supported
* Racket Expression Language
* Primitive Functions
* Top Level Definitions
* Modules

# Known missing (or partially complete) features
* Syntax Objects
* Syntax/Macro definitions
* Require/Provide Specifications
* Lots of optimizations

# Files

    LICENSE.txt                 -- The license file for this repo
    README.md                   -- This Readme File.
    info.rkt                    -- Package dependencies for this compiler
    main.rkt                    -- The compiler itself, including tests
    scribblings/compiler2.scrbl -- The (currently missing) documentation

[1]: http://nanopass.org
