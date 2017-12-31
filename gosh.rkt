#lang racket/base
(require (except-in racket/control set)
         "parse.rkt" "compile.rkt" "runtime.rkt"
         "bi.rkt"
         "toplevel.rkt"
         racket/async-channel racket/port readline/readline racket/match)
;         (for-syntax "runtime.rkt") (for-syntax "compile.rkt"))

                                        ;(provide run-gosh)
(provide run-gosh
         (all-from-out racket/base
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

(module+ main
         (parameterize
          [(current-namespace gosh-user-ns)]
          (let ([init-file (string-append (getenv "HOME") "/.goshrc")])
            (when (file-exists? init-file)
                  (gosh-load init-file)))
          (let ([args (current-command-line-arguments)])
            (if (= (vector-length args) 0)
                (repl)
                (with-input-from-string
                    (vector-ref args 0)
                  (lambda () (gosh-exec)))))))



