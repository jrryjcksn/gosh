#lang scribble/acmart acmlarge

@require["../gosh.rkt" "../compile-test.rkt" (prefix-in "!" (submod text-block/symbols unprefixed)) latex-utils/scribble/utils]

@(define (rarrow)
   (larger (larger (bold !Rightarrow))))

@(define (sexample str)
   @graybox[@bold[@emph[@colon-single-value[str]]]])

@title{Gosh: the Goal-Oriented Shell}

@author{Jerry R. Jackson}

@abstract{The basic command shell interface for POSIX-style systems has changed little since the original @bold{sh} program written by Stephen Bourne. A modern script in @bold{zsh} is largely identical. During that time, many "scripting languages" have been created to provide more complete programming facilities than those available in command shells.}

@section{Introduction}
@section{Two Modes}
@section{Single Address Space}
@section{Configuration as Code}
@section{Parsing}
@section{Calling Racket and Other Languages}
@section{Implementation}
@section{Examples}
@subsection{Collection intersection}
@bold{(fun intersect[$x, $y] -> @"@"(^$x == ^$y) end)[[1, 2, 3], [2, 3, 4]]}
@linebreak[] @rarrow[]
@sexample["(fun intersect[$x, $y] -> @(^$x == ^$y) end)[[1, 2, 3], [2, 3, 4]]"]

@subsection{Collection intersection with function shorthand}
@bold{@"@"({^$1 == ^$2}[[1, 2, 3], [2, 3, 4]])}
@linebreak[] @rarrow[]
@sexample["@({^$1 == ^$2}[[1, 2, 3], [2, 3, 4]])"]

@subsection{The first 6 prime numbers}
@bold["==> $p <- @*(2||3::%1+2 when !(% rem (^$p while % * % <= %%) == 0) while % < 17)"] @linebreak[] @rarrow[]
@sexample["==> $p <- @*(2||3::%1+2 when !(% rem (^$p while % * % <= %%) == 0) while % < 17)"]


