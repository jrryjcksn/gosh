#lang racket/base
(require (except-in racket/control set)
         array/dynamic
         (only-in racket/set set seteq set-member? set-add set-add! mutable-set set->list set-count)
         "parse.rkt" "compile.rkt" "runtime.rkt"
         "bi.rkt"
         "toplevel.rkt"
         racket/async-channel racket/port readline/readline racket/match)
;         (for-syntax "runtime.rkt") (for-syntax "compile.rkt"))

                                        ;(provide run-gosh)
(provide run-gosh
         eval-gosh
         (all-from-out racket/base
                       array/dynamic
                       "parse.rkt"
                       "runtime.rkt"
                       "compile.rkt"
                       "bi.rkt"
                       "toplevel.rkt"))

(set-gosh-executer! gosh-exec)
(define-namespace-anchor gosh-user-namespace-anchor)
(define gosh-user-ns (namespace-anchor->namespace gosh-user-namespace-anchor))

(define (run-gosh place-channel)
  (parameterize
   [(current-namespace gosh-user-ns)]
    (repl)))

(define (eval-gosh str)
  (with-input-from-string str gosh-exec))

(module+ main
         (parameterize
          [(current-namespace gosh-user-ns)]
          (let ([init-file (string-append (getenv "HOME") "/.goshrc")])
            (when (file-exists? init-file)
                  (gosh-load init-file)))
          (let ([args (current-command-line-arguments)])
            (if (= (vector-length args) 0)
                (repl)
                (eval-gosh (vector-ref args 0))))))



