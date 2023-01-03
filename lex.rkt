#lang racket/base


(require parser-tools/lex data/queue racket/trace racket/match racket/string
         racket/port)

(provide (except-out (all-defined-out)))
;(provide mllex)

(define-logger mllex)

(define-empty-tokens sym-tokens
  (COMMENT SQUOTE DQUOTE BQUOTE LPAR RPAR LBRACK RBRACK LBRACE RBRACE
           DOLLAR TAB NEWLINE COMMA SEMI SLASH BACKSLASH MATCH MINUS COLON
           TIMES DIV DOT EQUAL ONCE AT GT LT PIPE PIPEIN DOTDOT DOTDOTDOT
           AMP AMPAMP GTGT GTAMP HBRACK SBRACE COUNT IN WHEN WHILE REM NEG APP
           FUN NEXT END IF THEN ELSE FI ELIF newline EOF STRBOUND ATOMBOUND
           COLONLPAR COLONLBRACK DOTLPAR DOTLBRACK SETAT HASHAT STRAT CASE OF
           LOOP WITH HASHANON TO BY FROM &&> \|\|> IMPORT EXCEPT ONLY TRUE
           FALSE PIPEPIPE PIPEAMP = + - * / <. ^ ** // //* @ @* @: &+ & $ _ ::
           && &&. ||. &/ OR XOR ! != == > >= < <= ~ ~~ ~> <~ : :~> =! <! >! <?
           >? >~ :! => -> <- -= += ++ UPPIPEIN))

(define-tokens value-tokens (NUM ATOM FUNKYATOM VAR STR CHAR ANON SEQVAR REGEX
                                 RACKET SIMPLERACKET SYMBOL))

(define (make-sym-toks strs)
  (define symtab (make-hash))
  (define (mst str-list tab)
    (for ([binding (in-list str-list)])
         (match binding
           [(list s tok)
            (process-binding s 0 tab tok)]))
    tab)
  (define (process-binding s i t tok)
    (let ([last-index (sub1 (string-length s))]
          [char (string-ref s i)])
      (let ([existing (hash-ref t char #f)])
        (if (>= i last-index)
            (if existing
                (hash-set! t char (list (car existing) tok))
                (hash-set! t char (list #f tok)))
            (if existing
                (if (car existing)
                    (process-binding s (add1 i) (car existing) tok)
                    (let ([new-hash (make-hash)])
                      (hash-set! t char (list new-hash (cadr existing)))
                      (process-binding s (add1 i) new-hash tok)))
                (let ([new-hash (make-hash)])
                  (hash-set! t char (list new-hash #f))
                  (process-binding s (add1 i) new-hash tok)))))))
  (values (mst strs symtab)
          (let ([print-hash (make-hash)])
            (let loop ([strs-and-toks strs])
              (match strs-and-toks
                     [(list-rest (list str tok) remaining)
                      (hash-set! print-hash tok str)
                      (loop remaining)]
                     [_ print-hash])))))

(define-values (symtab printtab)
    (make-sym-toks
     `(("=" =)
       ("+" +)
       ("-" -)
       ("*" *)
       ("//" //)
       ("//*" //*)
       ("/" /)
       ("^" ^)
       ("**" **)
       ("*" *)
       ("@" @)
       ("@*" @*)
       ("@:" @:)
       ("&+" &+)
       ("&" &)
       ("$" $)
       ("_" _)
       ("::" ::)
       ("&&>" &&>)
       ("&&" &&)
       ("&&." &&.)
       ("&/" &/)
       ("||." ||.)
       ("||" OR)
       ("|||" XOR)
       ("||>" \|\|>)
       (";"  SEMI)
       ("!" !)
       ("!=" !=)
       ("==" ==)
       (">" >)
       (">=" >=)
       ("<" <)
       ("<=" <=)
       ("~" ~)
       ("~~" ~~)
       ("~>" ~>)
       ("<~" <~)
       (":" :)
       (":~>" :~>)
       ("=!" =!)
       ("<!" <!)
       (">!" >!)
       ("<?" <?)
       (">?" >?)
       (">~" >~)
       (":!" :!)
       ("=>" =>)
       ("->" ->)
       ("<-" <-)
       ("-=" -=)
       ("+=" +=)
       ("++" ++)
       ("<." <.)
       ("|"  ,(token-PIPE))
       ("|>" ,(token-PIPEIN))
       ("^|>" ,(token-UPPIPEIN))
       ("|&" ,(token-PIPEAMP))
       ("`"  ,(token-BQUOTE))
       ("."  ,(token-DOT))
       (".." ,(token-DOTDOT))
       ("..." ,(token-DOTDOTDOT))
       ("," ,(token-COMMA))
       ("(" ,(token-LPAR))
       (")" ,(token-RPAR))
       ;; ("&t" ,(token-TRUE))
       ;; ("&f" ,(token-FALSE))
       ("&[" ,(token-HBRACK))
       ("&{" ,(token-SBRACE))
       ("&{@}" ,(token-SETAT))
       ("&[@]" ,(token-HASHAT))
       ("&[%]" ,(token-HASHANON))
       ("\"@\"" ,(token-STRAT))
       ("{" ,(token-LBRACE))
       ("}" ,(token-RBRACE))
       ("[" ,(token-LBRACK))
       ("]" ,(token-RBRACK))
       ("%?" ,(token-COUNT)))))

(hash-set! printtab (token-LT) "<")
(hash-set! printtab (token-AMP) "&")
(hash-set! printtab (token-AMPAMP) "&&")
(hash-set! printtab (token-PIPEPIPE) "||")
(hash-set! printtab (token-PIPEAMP) "|&")

(define (lookup-sym str table last-index)
  (define (lookup-aux i t)
    (let* ([char (string-ref str i)]
           [entry (hash-ref t char #f)])
      (if (>= i last-index)
          (and entry (cadr entry))
          (and entry (car entry) (lookup-aux (add1 i) (car entry))))))
  (lookup-aux 0 table))

(define (lookup-longest str table)
  (define last-index (sub1 (string-length str)))
  (let loop ([index last-index])
    (let ([val (lookup-sym str table index)])
      (cond [val (values val (- last-index index))]
            [(> index 0) (loop (sub1 index))]
            [else (values #f #f)]))))

(define keywords ; add all special atoms and check the list whenever
                                        ; an atom is found to see if
                                        ; it's special (like '-')
    (hash "if"     'IF
          "elif"   'ELIF
          "else"   'ELSE
          "then"   'THEN
          "fi"     'FI
          "in"     'IN
          "fun"    'FUN
          "when"   'WHEN
          "while"  'WHILE
          "next"   'NEXT
          "import" 'IMPORT
          "except" 'EXCEPT
          "only"   'ONLY
          "rem"    'REM
          "end"    'END
          "case"   'CASE
          "of"     'OF
          "to"     'TO
          "by"     'BY
          "from"     'FROM
          "loop"   'LOOP
          "with"   'WITH
          "-"      '-
          "/"      (token-DIV)
          "."      (token-DOT)))

(define (mllex in-item initial-mode)
  (define item (string-append in-item " "))
  (define acc #f)
  (define ch #f)
  (define pending-tokens (make-queue))
  (define offset 0)
  (define line 1)
  (define col 0)
  (define tok-start #f)
  (define tok-start-line #f)
  (define tok-start-col #f)
  (define next-state #f)
  (define seen-eof? #f)
  (define (is-dquote? x) (eqv? x #\"))
  (define (is-atom-end? x)
    (enter 'is-atom-end? x)
    (match x
           [(or 'EOF #\tab #\space #\newline #\" #\' #\` #\> #\<
                #\| #\& #\; #\) #\])
            #t]
           [_ #f]))
  (define stack '())
  (define str-bound? is-dquote?)
  (define str-bound-stack '())
  (define str-bound-depth 0)
  (define brackets '())
  (define modes '())
  (define mode #f)

  (define (stacks)
    (log-mllex-debug
     "STACK: ~s, BOUNDS: ~s, BOUND: ~s, BRACK: ~s, MODES: ~s, MODE: ~s"
     stack str-bound-stack str-bound? brackets modes mode))

  (define (push-str-bound! boundfun)
    (log-mllex-debug "pushing: ~s onto: ~s~n" boundfun str-bound-stack)
    (set! str-bound-stack (cons str-bound? str-bound-stack))
    (set! str-bound? boundfun)
    (set! str-bound-depth (add1 str-bound-depth)))

  (define (pop-str-bound!)
    (log-mllex-debug "popping from: ~s~n" str-bound-stack)
    (set! str-bound? (car str-bound-stack))
    (set! str-bound-stack (cdr str-bound-stack))
    (set! str-bound-depth (sub1 str-bound-depth)))

  (define (pos-token tok)
    (let ([result (position-token
                   tok
                   (position tok-start tok-start-line tok-start-col)
                   (position offset line col))])
      result))

  (define (switch-mode)
    (pause (if (eq? mode start) str-start start)))

  (define (save state)
    (set! stack (cons state stack)))

  (define (restore)
    (begin0
     (car stack)
     (set! stack (cdr stack))))

  (define (stack-null?)
    (eq? stack '()))

  (define (push brack)
    (set! brackets (cons brack brackets)))

  (define (pop)
    (begin0
     (car brackets)
     (set! brackets (cdr brackets))))

  (define (push-mode m)
    (set! modes (cons m modes)))

  (define (pop-mode)
    (begin0
     (car modes)
     (set! modes (cdr modes))))

  (define (pause state)
    (log-mllex-debug "PAUSING: ~s~%" state)
    (set! next-state state))

  (define (resume)
    (log-mllex-debug "RESUMING: NP=~s, NS=~s~%" next-pending next-state)
    (let ([result (or (next-pending) (next-state))])
      (log-mllex-info "TOKEN: ~s" result)
      result))

  (define (next state)
    (next-char)
    (state))

  (define (next-pending)
    (let ([result (and (not (queue-empty? pending-tokens))
                       (dequeue! pending-tokens))])
      (when result
            (log-mllex-debug "NEXT PENDING: ~s" result))
      result))

  (define (pend token) (enqueue! pending-tokens token))

  (define (next-char)
    (enter 'next-char ch)
    (cond [seen-eof? (set! ch 'EOF)]
          [(>= offset (string-length item))
           (forward #\.)
           (set! seen-eof? #t)
           (set! ch 'EOF)]
          [#t
           (set! ch (string-ref item offset))
           (forward ch)]))

  (define (forward ch)
    (set! offset (add1 offset))
    (if (eqv? ch #\newline)
        (inc-line)
        (inc-pos)))

  (define (backward n)
    (set! seen-eof? #f)
    (set! offset (- offset n))
    (set! col (- col n))
    (set! ch (string-ref item (sub1 offset))))

  (define (start-token)
    (set! acc (open-output-string))
    (set! tok-start offset)
    (set! tok-start-line line)
    (set! tok-start-col col))

  (define (start-token-backward n)
    (set! acc (open-output-string))
    (set! tok-start (- offset n))
    (set! tok-start-line line)
    (set! tok-start-col (- col n)))

  (define (accumulate ch) (display ch acc))

  (define (accumulate-and-switch-state state)
    (accumulate ch)
    (next state))

  (define (collect-chars) (get-output-string acc))

  (define (inc-line)
    (set! line (add1 line))
    (set! col 1))

  (define (inc-pos)
    (set! col (add1 col)))

  (define (char-literal-token)
    (pos-token (token-CHAR (string-ref (collect-chars) 0))))

  (define (boolean-token val)
    (lambda () (enter 'bt val)
            (pos-token (if val (token-TRUE) (token-FALSE)))))

  (define (num-token)
    (pos-token (token-NUM (string->number (collect-chars)))))

  (define (imag-token)
    (pos-token (token-NUM (string->number
                           (string-append "+" (collect-chars))))))

  (define (symbol-token)
    (pos-token (token-SYMBOL (string->symbol (collect-chars)))))

  (define (atom-token)
    (explicit-atom-token (collect-chars)))

  (define (explicit-atom-token atom-string)
    (enter 'explicit-atom-token atom-string)
    (define keyword-val (hash-ref keywords atom-string #f))
    (if (and (eq? mode start) keyword-val)
        (pos-token keyword-val)
;        (pos-token (token-ATOM (string->symbol atom-string)))))
        (pos-token (token-ATOM atom-string))))

  (define (funky-atom-token)
    (pos-token ((if (eq? mode start) token-ATOM token-FUNKYATOM)
                (string-trim (collect-chars) "'"))))

  (define (str-token)
    (pos-token (token-STR (collect-chars))))

  (define (anon-token)
    (pos-token (token-ANON (string->symbol (collect-chars)))))

  (define (count-token)
    (pos-token (token-COUNT)))

  (define (seqvar-token)
    (pos-token (token-SEQVAR (string->symbol (collect-chars)))))

  (define (regex-token)
    (pos-token (token-REGEX (collect-chars))))

  (define (str-bound-token)
    (pos-token (token-STRBOUND)))

  (define (str-at-token)
    (pos-token (token-STRAT)))

  (define (atom-bound-token)
    (position-token (token-ATOMBOUND)
                    (position tok-start tok-start-line tok-start-col)
                    (position tok-start tok-start-line tok-start-col)))

  (define (racket-token)
    (pos-token (token-RACKET (collect-chars))))

  (define (simple-racket-token)
    (pos-token (token-SIMPLERACKET (collect-chars))))

  (define (var-brace-token)
    (var-token-helper #t))

  (define (var-token)
    (var-token-helper #f))

  (define (var-token-helper remove-braces)
    (let ([varstr (collect-chars)])
      (pos-token
       (token-VAR
        (string->symbol
         (if remove-braces
             (string-append
              "$"
              (substring varstr 2 (sub1 (string-length varstr))))
             varstr))))))

  ;; Create a new position struct that is translated one character forward
  ;; in the current line.
  (define (inc-position pos)
    (position (add1 (position-offset pos))
              (position-line pos)
              (add1 (position-col pos))))

  (define (enter state-name ch . other-args)
    (if (null? other-args)
        (log-mllex-debug "ENTERING: ~s, ch = ~s" state-name ch)
        (log-mllex-debug "ENTERING: ~s, ch = ~s, other-args = ~s"
                         state-name ch other-args)))

  (define (handle-num-imag)
    (accumulate ch)
    (next-char)
    (pause start)
    (imag-token))

  (define (mismatch? ch)
    (let [(brack (pop))]
      (or (eq? brack ch)
          (bracket-exception brack ch))))

  (define (bracket-exception brack ch)
    (raise
     (make-exn:fail:read
      (with-output-to-string
        (lambda ()
          (printf
           "Parentheses and brackets not nested properly: ~s and ~s."
           brack ch)))
      (current-continuation-marks)
      (list (make-srcloc ch line (sub1 col) offset 1)))))

  (define (comment)
    (enter 'comment ch)
    (match ch
          ['EOF
           (start-token)
           (pos-token 'EOF)]
          [#\newline (next start)]
          [_ (next comment)]))

  (define (start)
    (enter 'start ch)
;    (or (next-pending)
        (match ch
          ['EOF
           (start-token)
           (pos-token 'EOF)]
          [#\# (next comment)]
          [(or #\space #\tab #\newline) (next start)]
          [(? char-numeric?)
           (start-token)
           (accumulate-and-switch-state num)]
          [#\-
           (start-token)
           (accumulate-and-switch-state atom-or-minus-sym)]
          [(? char-alphabetic?)
           (start-token)
           (accumulate-and-switch-state atom)]
          [#\_
           (start-token)
           (accumulate-and-switch-state atom-or-sym)]
          ;; [(or #\_ #\/ #\.)
          ;;  (start-token)
          ;;  (accumulate-and-switch-state atom-or-sym)]
          [#\'
           (start-token)
           (accumulate-and-switch-state funky-atom)]
          [#\"
             (start-token)
             (next str-or-str-at-return)]
          [#\)
           (mismatch? #\()
           (begin0
            (single-char-token token-RPAR)
            (set! mode (pop-mode))
            (pause (restore)))]
          [#\]
           (mismatch? #\[)
           (begin0
            (single-char-token token-RBRACK)
            (set! mode (pop-mode))
            (pause (restore)))]
           ;; (pause (restore))
           ;; (next-char)
           ;; (begin0 (pos-token (token-RPAR))
           ;;      (next-char))]
          [#\$
           (start-token)
           (next var-or-regex)]
          [#\%
           (start-token)
           (accumulate-and-switch-state anon-or-seq)]
          [#\?
           (start-token)
           (next char-literal)]
          ;; [#\{
          ;;  (switch-mode)
          ;;  (token-LBRACE)]
          [#\(
           (start-token)
           (next maybe-racket)]
          [#\{
           (start-token)
           (next maybe-simple-racket)]
          [#\&
           (start-token)
           (next maybe-boolean-or-symbol)]
          [_
           (start-token)
           (accumulate-and-switch-state symtok)]))

  (define (maybe-boolean-or-symbol)
    (enter 'maybe-boolean-or-symbol ch)
    (match ch
           ['EOF (symtok)]
           [#\! (accumulate-and-switch-state boolean)]
           [(and (? char?)
                 (or (? char-alphabetic?)
                     (? char-numeric?)
                     #\_
                     #\-))
            (backward 1)
            (accumulate-and-switch-state symbol)]
           [_
            (backward 1)
            (accumulate-and-switch-state symtok)]))

  (define (boolean)
    (enter 'boolean ch)
    (match ch
           ['EOF (symtok)]
           [#\t
            (pause start)
            (next-finish (boolean-token #t))]
           [#\f
            (pause start)
            (next-finish (boolean-token #f))]
           [_ (accumulate-and-switch-state symtok)]))

  (define (maybe-bool val)
    (enter 'maybe-bool ch)
    (match ch
           ['EOF
            (finish-token (boolean-token val))]
           [(and (? char?)
                 (or (? char-alphabetic?)
                     (? char-numeric?)
                     #\_
                     #\-))
            (accumulate #\&)
            (accumulate (if val #\t #\f))
            (accumulate-and-switch-state symbol)]
           [_
            (pause start)
            (next-finish (boolean-token val))]))


  (define (symbol)
    (enter 'symbol ch)
    (match ch
           ['EOF (finish-token symbol-token)]
           [(and (? char?)
                 (or (? char-alphabetic?)
                     (? char-numeric?)
                     #\_
                     #\-))
            (accumulate-and-switch-state symbol)]
           [_ (finish-token symbol-token)]))

  (define (maybe-racket)
    (enter 'maybe-racket ch)
    (match ch
           ['EOF
            (raise (make-exn:fail:read (list (make-srcloc
                                              item
                                              line
                                              (sub1 col)
                                              offset
                                              1))))]
           [#\;
            (start-token)
            (next racket)]
           [_
            (backward 1)
            (accumulate-and-switch-state symtok)]))

  (define (racket)
    (enter 'racket ch)
    (match ch
           ['EOF
            (raise (make-exn:fail:read (list (make-srcloc
                                              item
                                              line
                                              (sub1 col)
                                              offset
                                              1))))]
           [#\;
            (next maybe-not-racket)]
           [_
            (accumulate-and-switch-state racket)]))

  (define (maybe-not-racket)
    (enter 'maybe-not-racket ch)
    (match ch
           ['EOF
            (raise (make-exn:fail:read (list (make-srcloc
                                              item
                                              line
                                              (sub1 col)
                                              offset
                                              1))))]
           [#\)
            (begin0
             (next-finish racket-token)
             (pause start))]
           [_
            (backward 1)
            (accumulate-and-switch-state racket)]))

  (define (maybe-simple-racket)
    (enter 'maybe-simple-racket ch)
    (match ch
           ['EOF
            (raise (make-exn:fail:read (list (make-srcloc
                                              item
                                              line
                                              (sub1 col)
                                              offset
                                              1))))]
           [#\;
            (start-token)
            (next simple-racket)]
           [_
            (backward 1)
            (accumulate-and-switch-state symtok)]))

  (define (simple-racket)
    (enter 'simple-racket ch)
    (match ch
           ['EOF
            (raise (make-exn:fail:read (list (make-srcloc
                                              item
                                              line
                                              (sub1 col)
                                              offset
                                              1))))]
           [#\;
            (next maybe-not-simple-racket)]
           [_
            (accumulate-and-switch-state simple-racket)]))

  (define (maybe-not-simple-racket)
    (enter 'maybe-not-simple-racket ch)
    (match ch
           ['EOF
            (raise (make-exn:fail:read (list (make-srcloc
                                              item
                                              line
                                              (sub1 col)
                                              offset
                                              1))))]
           [#\}
            (begin0
             (next-finish simple-racket-token)
             (pause start))]
           [_
            (backward 1)
            (accumulate-and-switch-state simple-racket)]))

  (define (token-ends-with? ch)
    (define str (collect-chars))
    (log-mllex-debug "token-ends-with?: ~s" str)
    (eqv? (string-ref str (sub1 (string-length str))) ch))

  (define (next-finish tokfun)
    (next-char)
    (finish-token tokfun))

  (define (char-literal)
    (enter 'char-literal ch)
    (match ch
           ['EOF
            (raise (make-exn:fail:read (list (make-srcloc
                                              item
                                              line
                                              (sub1 col)
                                              offset
                                              1))))]
           [#\\
            (next char-literal-escape)]
           [_
            (accumulate ch)
            (next-finish char-literal-token)]))

(define (char-literal-escape)
    (enter 'char-literal-escape ch)
    (match ch
           ['EOF
            (raise (make-exn:fail:read (list (make-srcloc
                                              item
                                              line
                                              (sub1 col)
                                              offset
                                              1))))]
           [#\n
            (accumulate #\newline)
            (next-finish char-literal-token)]
           [#\r
            (accumulate #\return)
            (next-finish char-literal-token)]
           [#\t
            (accumulate #\tab)
            (next-finish char-literal-token)]
           [#\b
            (accumulate #\backspace)
            (next-finish char-literal-token)]
           [#\s
            (accumulate #\space)
            (next-finish char-literal-token)]
           [_
            (accumulate ch)
            (next-finish char-literal-token)]))

  (define (symtok)
    (enter 'symtok ch)
    (match ch
      [(or 'EOF (? char-alphabetic?) (? char-numeric?) (? char-whitespace?))
       (log-mllex-debug "symtok: so far -- ~s" (collect-chars))
       (let*-values ([(tokstr) (collect-chars)]
                     [(tok decrement) (lookup-longest tokstr symtab)])
         (if tok
             (begin
               (when (> decrement 0)
                 (backward decrement)
                 (log-mllex-debug "after dec(~s): ~s" decrement
                                  (substring item offset)))
               (cond [(eq? tok (token-LPAR))
                      (save mode)
                      (push #\()
                      (push-mode mode)]
                     [(or (eq? tok (token-LBRACK))
                          (eq? tok (token-HBRACK)))
                      (save mode)
                      (push #\[)
                      (push-mode mode)])
               (pause mode)
               (pos-token tok))
             (raise (make-exn:fail:read (list (make-srcloc
                                               item
                                               line
                                               (sub1 col)
                                               offset
                                               1))))))]
      [_
       (accumulate-and-switch-state symtok)]))

(define (str-comment)
    (enter 'str-comment ch)
    (match ch
          ['EOF
           (start-token)
           (pos-token 'EOF)]
          [#\newline (next str-start)]
          [_ (next str-comment)]))

  (define (str-start)
    (enter 'str-start ch)
    ;; (or
    ;;  (next-pending)
     (match ch
            ['EOF
             (pos-token 'EOF)]
            [#\# (next str-comment)]
            [(or #\tab #\space)
             (next str-start)]
            [#\;
             (single-char-token token-SEMI)]
            [#\<
             (single-char-token token-LT)]
            [#\>
             (start-token)
             (accumulate-and-switch-state redirect)]
            [#\&
             (start-token)
             (accumulate-and-switch-state amp)]
            [#\|
             (start-token)
             (accumulate-and-switch-state pipe)]
            [#\$
             (begin0
              (zero-char-token token-ATOMBOUND)
              (push-str-bound! is-atom-end?)
              (start-token)
              (next-char)
;              (accumulate #\$)
              (pause str-dollar))]
            [#\)
             (mismatch? #\()
             (begin0
              (single-char-token token-RPAR)
              (set! mode (pop-mode))
              (pause (restore)))]
            [#\]
             (mismatch? #\[)
             (begin0
              (single-char-token token-RBRACK)
              (set! mode (pop-mode))
              (pause (restore)))]
            [#\"
             (start-token)
             (begin0
                 (next-finish str-bound-token)
               (push-str-bound! is-dquote?)
               (pause str-return))]
            [#\'
             (start-token)
             (accumulate-and-switch-state funky-atom)]
            [_
             (start-token)
             (accumulate-and-switch-state shell-atom)]))

  (define (str-or-str-at-return)
    (enter 'str-or-str-at-return ch)
    (match ch
      [#\@ (next str-at-return)]
      [_ (begin0
             (finish-token str-bound-token)
           (push-str-bound! is-dquote?)
           (pause str-return))]))

  (define (str-at-return)
    (enter 'str-at-return ch)
    (match ch
      [#\"
       (next-finish str-at-token)]
      [_ (backward 1)
         (str-return)]))

  (define (str-return)
;    (or (next-pending)
        (begin
          (start-token)
          (str)))

  ;; (define (str-start-return)
  ;;   (begin
  ;;     (start-token)
  ;;     (str-start)))

  (define (shell-atom)
    (enter 'shell-atom ch)
    (match ch
           [(or 'EOF #\tab #\space #\newline #\" #\' #\> #\< #\| #\& #\;)
            (finish-token atom-token)]
           [#\$
            (when (> offset tok-start)
                  (pend (finish-token str-token)))
            (begin0
             (zero-char-token token-ATOMBOUND)
             (push-str-bound! is-atom-end?)
             (start-token)
             (next-char)
             (pause str-dollar))]
           [#\)
            (mismatch? #\()
            (begin0
             (finish-token atom-token)
             (pend (single-char-token token-RPAR))
             (set! mode (pop-mode))
             (pause (restore)))]
           [#\]
            (let ([brack (pop)])
              (case brack
                [(#\<) (accumulate-and-switch-state shell-atom)]
                [(#\[)
                 (begin0
                  (finish-token atom-token)
                  (pend (single-char-token token-RBRACK))
                  (set! mode (pop-mode))
                  (pause (restore)))]
                [else (bracket-exception brack #\[)]))]
           [#\[
            (push #\<)
            (accumulate-and-switch-state shell-atom)]
           [#\\
            (next-char)
            (accumulate-and-switch-state shell-atom)]
           [_
            (accumulate-and-switch-state shell-atom)]))

  (define (zero-char-token token-constructor)
    (start-token)
    (finish-token
     (lambda ()
       (position-token (token-constructor)
                       (position tok-start tok-start-line tok-start-col)
                       (position tok-start tok-start-line tok-start-col)))))

  (define (single-char-token token-constructor)
    (start-token)
    (next-finish (lambda () (pos-token (token-constructor)))))

  (define (double-char-token token-constructor)
    (start-token)
    (accumulate ch)
    (next-char)
    (next-finish (lambda () (pos-token (token-constructor)))))

  (define (finish-token token-constructor)
    (pause mode)
    (token-constructor))

  (define (redirect)
    (enter 'redirect ch)
    (match ch
           [#\>
            (accumulate #\>)
            (next-finish (lambda () (pos-token (token-GTGT))))]
           [#\&
            (accumulate #\&)
            (next-finish (lambda () (pos-token (token-GTAMP))))]
           [_
            (finish-token (lambda () (pos-token (token-GT))))]))

  (define (amp)
    (enter 'amp ch)
    (match ch
           [#\&
            (accumulate #\&)
            (next-finish (lambda () (pos-token (token-AMPAMP))))]
           [_
            (finish-token (lambda () (pos-token (token-AMP))))]))

  (define (pipe)
    (enter 'pipe ch)
    (match ch
           [#\|
            (accumulate #\|)
            (next-finish (lambda () (pos-token (token-PIPEPIPE))))]
           [#\&
            (accumulate #\&)
            (next-finish (lambda () (pos-token (token-PIPEAMP))))]
           [_
            (finish-token (lambda () (pos-token (token-PIPE))))]))

  (define (str-var-simple)
    (enter 'str-var-simple ch)
    (match ch
      [(and (? char?)
            (or (? char-alphabetic?)
                (? char-numeric?)
                #\_))
       (accumulate-and-switch-state str-var-simple)]
      [_
       (pause str-return)
       (var-token)]))

  (define (str-var-digits)
    (enter 'str-var-digits ch)
    (match ch
      [(and (? char?)
            (? char-numeric?))
       (accumulate-and-switch-state str-var-digits)]
      [_
       (pause str-return)
       (var-token)]))

  (define (str-var-brace)
    (enter 'str-var-brace ch)
    (match ch
      ['EOF
       (pause mode)
       (pos-token 'EOF)]
      [#\}
       (accumulate ch)
       (next-char)
       (pause str-return)
       (var-brace-token)]
      [(or (? char-alphabetic?)
           (? char-numeric?)
           #\_)
       (accumulate-and-switch-state str-var-brace)]
      [_
       (raise (make-exn:fail:read (list (make-srcloc
                                         item
                                         line
                                         (sub1 col)
                                         offset
                                         1))))]))

(define (str-var)
    (enter 'str-var ch)
    (match ch
      ['EOF
       (pause mode)
       (pos-token 'EOF)]
      [#\{
       (accumulate-and-switch-state str-var-brace)]
      [(and val (or #\$ #\* #\?))
       (accumulate val)
       (next-char)
       (pause str-return)
       (var-token)]
      [(? char-numeric?)
       (accumulate-and-switch-state str-var-digits)]
      [(? char-alphabetic?)
       (accumulate-and-switch-state str-var-simple)]
      [_
       (accumulate-and-switch-state str)]))

  (define (str)
    (enter 'str ch)
    (match ch
      ['EOF #:when (not (str-bound? 'EOF))
            (raise (make-exn:fail:read (list (make-srcloc
                                              item
                                              line
                                              (sub1 col)
                                              offset
                                              1))))]
      [#\$
       ;; (begin0 (single-char-token token-DOLLAR)
       ;;         (pause str-dollar))]
       (next str-dollar)]
      [#\\
       (next-char)
       (accumulate-and-switch-state str)]
      [(? str-bound?)
       (log-mllex-debug "IN STR -- bounds: ~s, modes: ~s~n"
                        str-bound-stack modes)
       (handle-str-end)]
      [_
       (accumulate-and-switch-state str)]))

  (define (handle-str-end)
    (if (<= offset tok-start)
        (finish-str)
        (begin0
            (finish-token str-token)
          (pause finish-str))))

  (define (finish-str) (begin0 (str-end) (pop-str-bound!)))

  (define (str-dollar)
    (enter 'str-dollar ch)
    (match ch
      ['EOF
       (raise (make-exn:fail:read (list (make-srcloc
                                         item
                                         line
                                         (sub1 col)
                                         offset
                                         1))))]
      [#\:
       (next str-dollar-colon)]
      [#\.
       (next str-dollar-dot)]
      [#\(
       (backward 1)
       (if (> offset tok-start)
           (begin0
            (finish-token str-token)
            (pause pre-str-dollar-lparen))
           (pre-str-dollar-lparen))]
      [#\[
       (backward 1)
       (if (> offset tok-start)
           (begin0
            (finish-token str-token)
            (pause pre-str-dollar-lbrack))
           (pre-str-dollar-lbrack))]
      [_
       (if (not (equal? (collect-chars) ""))
           (begin0
            (finish-token str-token)
            (start-token)
            (accumulate #\$)
            (pause str-var))
           (begin
;             (start-token)
             (accumulate #\$)
             (str-var)))]))
       ;; (begin0
       ;;  (str-token)
       ;;  (start-token)
       ;;  (accumulate #\$)
       ;;  (pause str-var))]))

  (define (str-dollar-colon)
    (match ch
      ['EOF
       (raise (make-exn:fail:read (list (make-srcloc
                                         item
                                         line
                                         (sub1 col)
                                         offset
                                         1))))]
      [#\(
       (backward 2)
       (if (> offset tok-start)
           (begin0
            (finish-token str-token)
            (pause pre-str-dollar-colon-lparen))
           (pre-str-dollar-colon-lparen))]
      [#\[
       (backward 2)
       (if (> offset tok-start)
           (begin0
            (finish-token str-token)
            (pause pre-str-dollar-colon-lbrack))
           (pre-str-dollar-colon-lbrack))]
      ['EOF
       (raise (make-exn:fail:read (list (make-srcloc
                                         item
                                         line
                                         (sub1 col)
                                         offset
                                         1))))]))

  (define (pre-str-dollar-colon-lparen)
    (begin0
     (single-char-token token-DOLLAR)
     (pend (double-char-token token-COLONLPAR))
     (save str-return)
     (push #\()
     (push-mode mode)
;     (push-mode start)
     (pause str-dollar-colon-lparen)))

  (define (str-dollar-colon-lparen)
    (enter 'str-dollar-colon-lparen ch)
    (match ch
      ['EOF
       (raise (make-exn:fail:read (list (make-srcloc
                                         item
                                         line
                                         (sub1 col)
                                         offset
                                         1))))]
      [_
       (set! mode start)
       (start)]))

  (define (pre-str-dollar-colon-lbrack)
    (begin0
     (single-char-token token-DOLLAR)
     (pend (double-char-token token-COLONLBRACK))
     (save str-return)
     (push #\[)
     (push-mode mode)
     (pause str-dollar-colon-lbrack)))

  (define (str-dollar-colon-lbrack)
    (enter 'str-dollar-colon-lbrack ch)
    (match ch
      ['EOF
       (raise (make-exn:fail:read (list (make-srcloc
                                         item
                                         line
                                         (sub1 col)
                                         offset
                                         1))))]
      [_
       (set! mode start)
       (start)]))

  (define (str-dollar-dot)
    (match ch
      ['EOF
       (raise (make-exn:fail:read (list (make-srcloc
                                         item
                                         line
                                         (sub1 col)
                                         offset
                                         1))))]
      [#\(
       (backward 2)
       (if (> offset tok-start)
           (begin0
            (finish-token str-token)
            (pause pre-str-dollar-dot-lparen))
           (pre-str-dollar-dot-lparen))]
      [#\[
       (backward 2)
       (if (> offset tok-start)
           (begin0
            (finish-token str-token)
            (pause pre-str-dollar-dot-lbrack))
           (pre-str-dollar-dot-lbrack))]))

  (define (pre-str-dollar-dot-lparen)
    (begin0
     (single-char-token token-DOLLAR)
     (pend (double-char-token token-DOTLPAR))
     (save str-return)
     (push #\()
     (push-mode mode)
     (pause str-dollar-dot-lparen)))

  (define (str-dollar-dot-lparen)
    (enter 'str-dollar-dot-lparen ch)
    (match ch
      ['EOF
       (raise (make-exn:fail:read (list (make-srcloc
                                         item
                                         line
                                         (sub1 col)
                                         offset
                                         1))))]
      [_
       (set! mode str-start)
       (str-start)]))

  (define (pre-str-dollar-dot-lbrack)
    (begin0
     (single-char-token token-DOLLAR)
     (pend (double-char-token token-DOTLBRACK))
     (save str-return)
     (push #\[)
     (push-mode mode)
     (pause str-dollar-dot-lbrack)))

  (define (str-dollar-dot-lbrack)
    (enter 'str-dollar-dot-lbrack ch)
    (match ch
      ['EOF
       (raise (make-exn:fail:read (list (make-srcloc
                                         item
                                         line
                                         (sub1 col)
                                         offset
                                         1))))]
      [_
       (set! mode str-start)
       (str-start)]))

  (define (pre-str-dollar-lparen)
    (begin0
     (single-char-token token-DOLLAR)
     (pend (single-char-token token-LPAR))
     (save str-return)
     (push #\()
     (push-mode mode)
     (pause str-dollar-lparen)))

  (define (str-dollar-lparen)
    (enter 'str-dollar-lparen ch)
    (match ch
      ['EOF
       (raise (make-exn:fail:read (list (make-srcloc
                                         item
                                         line
                                         (sub1 col)
                                         offset
                                         1))))]
      [_
       (mode)]))

  (define (pre-str-dollar-lbrack)
    (begin0
     (single-char-token token-DOLLAR)
     (pend (single-char-token token-LBRACK))
;     (save str-start-return)
     (save str-return)
     (push #\[)
     (push-mode mode)
     (pause str-dollar-lparen)))

  (define (str-end)
    (enter 'str-end ch)
    (begin0
     (single-char-token token-STRBOUND)
     (unless (eq? str-bound? is-dquote?)
             (backward 1))
     (pause mode)))

  (define (anon-or-seq)
    (enter 'anon-or-seq ch)
    (match ch
      ['EOF
       (finish-token anon-token)]
      [#\%
       (accumulate-and-switch-state anon)]
      [#\?
       (next-finish count-token)]
      [(? char-numeric?)
       (accumulate-and-switch-state seqvar)]
      [_
       (finish-token anon-token)]))

(define (anon)
    (enter 'anon ch)
    (match ch
      ['EOF
       (finish-token anon-token)]
      [#\%
       (accumulate-and-switch-state anon)]
      [_
       (finish-token anon-token)]))

  (define (seqvar)
    (enter 'seqvar ch)
    (match ch
      [(and (? char?) (? char-numeric?))
       (accumulate-and-switch-state seqvar)]
      [_
       (finish-token seqvar-token)]))

  (define (var-or-regex)
    (enter 'var-or-regex (list ch (char->integer ch)))
    (match ch
      ['EOF
       (pause mode)
       (pos-token 'EOF)]
      [#\"
       (backward 1)
       (begin0
        (single-char-token token-DOLLAR)
        (push-str-bound! is-dquote?)
        (pend (single-char-token token-STRBOUND))
        (pause str))]
      [#\'
       (backward 1)
       (begin0
        (single-char-token token-DOLLAR)
        (start-token)
        (accumulate #\')
        (next-char)
        (pause funky-atom))]
      [_
       (accumulate #\$)
       (var)]))

  (define (var)
    (enter 'var ch)
    (match ch
      ['EOF
       (pause mode)
       (pos-token 'EOF)]
      [#\{
       (accumulate-and-switch-state var-brace)]
      [#\.
       (next-char)
       (dollar-x token-DOTLPAR token-DOTLBRACK dollar-dot-lparen)]
      [#\:
       (next-char)
       (dollar-x token-COLONLPAR token-COLONLBRACK dollar-colon-lparen)]
      [#\(
       (backward 1)
       (pre-dollar token-LPAR #\()]
      [#\[
       (backward 1)
       (pre-dollar token-LBRACK #\[)]
      [(and val (or #\$ #\* #\?))
       (accumulate val)
       (next-finish var-token)]
      [(? char-numeric?)
       (accumulate-and-switch-state var-digits)]
      [(? char-alphabetic?)
       (accumulate-and-switch-state var-simple)]))

(define (dollar-x par-tok brack-tok fun)
    (enter 'dollar-x ch par-tok brack-tok fun)
    (match ch
      [#\(
       (backward 2)
       (pre-dollar-x par-tok fun #\()]
      [#\[
       (backward 2)
       (pre-dollar-x brack-tok fun #\[)]
      [_
       (raise (make-exn:fail:read (list (make-srcloc
                                         item
                                         line
                                         (sub1 col)
                                         offset
                                         1))))]))

(define (pre-dollar-x tok pausefun char)
    (enter 'pre-dollar-x ch tok pausefun char)
    (begin0
     (single-char-token token-DOLLAR)
     (pend (double-char-token tok))
     (save mode)
     (push char)
     (push-mode mode)
     (pause pausefun)))

  (define (pre-dollar tok char)
    (enter 'pre-dollar ch tok char)
    (begin0
     (single-char-token token-DOLLAR)
     (pend (single-char-token tok))
     (save mode)
     (push char)
     (push-mode mode)
     (pause dollar-lparen)))

  (define (dollar-dot-lparen)
    (enter 'dollar-dot-lparen ch)
    (match ch
      ['EOF
       (raise (make-exn:fail:read
               "EOF after '$.('"
               (current-continuation-marks)
               (list (make-srcloc
                      item
                      line
                      (sub1 col)
                      offset
                      1))))]
      [_
       (set! mode str-start)
       (str-start)]))

  (define (dollar-colon-lparen)
    (enter 'dollar-colon-lparen ch)
    (match ch
      ['EOF
       (raise (make-exn:fail:read
               "EOF after '$:('"
               (current-continuation-marks)
               (list (make-srcloc
                      item
                      line
                      (sub1 col)
                      offset
                      1))))]
      [_
       (set! mode start)
       (start)]))

  (define (dollar-lparen)
    (enter 'dollar-lparen ch)
    (match ch
      ['EOF
       (raise (make-exn:fail:read
               "EOF after '$('"
               (current-continuation-marks)
               (list (make-srcloc
                      item
                      line
                      (sub1 col)
                      offset
                      1))))]
      [_
       (mode)]))

  (define (regex)
    (enter 'regex ch)
    (match ch
      ['EOF
       (raise (make-exn:fail:read
               "EOF in regular expression"
               (current-continuation-marks)
               (list (make-srcloc
                      item
                      line
                      (sub1 col)
                      offset
                      1))))]
      [#\\
       (next regex-quote)]
      [#\"
       (next-char)
       (finish-token regex-token)]
      [_
       (accumulate-and-switch-state regex)]))

  (define (regex-quote)
    (match ch
      ['EOF
       (raise (make-exn:fail:read
               "EOF after '\\' in regular expression"
               (current-continuation-marks)
               (list (make-srcloc
                      item
                      line
                      (sub1 col)
                      offset
                      1))))]
      [#\"
       (accumulate-and-switch-state regex)]
      [_
       (accumulate #\\)
       (accumulate-and-switch-state regex)]))

  (define (var-simple)
    (enter 'var-simple ch)
    (match ch
      [(and (? char?)
            (or (? char-alphabetic?)
                (? char-numeric?)
                #\_))
       (accumulate-and-switch-state var-simple)]
      [_
       (finish-token var-token)]))

  (define (var-digits)
    (enter 'var-digits ch)
    (match ch
      [(and (? char?)
            (? char-numeric?))
       (accumulate-and-switch-state var-digits)]
      [_
       (finish-token var-token)]))

  (define (var-brace)
    (enter 'var-brace ch)
    (match ch
      ['EOF
       (pause mode)
       (pos-token 'EOF)]
      [#\}
       (accumulate ch)
       (next-char)
       (finish-token var-brace-token)]
      [(or (? char-alphabetic?)
           (? char-numeric?)
           #\_)
       (accumulate-and-switch-state var-brace)]
      [_
       (raise (make-exn:fail:read (list (make-srcloc
                                         item
                                         line
                                         (sub1 col)
                                         offset
                                         1))))]))

  (define (atom-or-minus-sym)
    (enter 'atom-or-minus-sym ch)
    (match ch
      ['EOF
       (finish-token (lambda () (pos-token '-)))]
      [(or #\> #\=)
       (accumulate-and-switch-state symtok)]
      ;; [(or (? char-alphabetic?) #\_ #\/ #\. #\- #\+)
      ;;  (accumulate-and-switch-state atom)]
      [(? char-numeric?)
       (pause num)
       (begin0 (pos-token '-)
               (start-token))]
      [_
       (finish-token (lambda () (pos-token '-)))]))

  (define (atom-or-sym)
    (enter 'atom-or-sym ch)
    (match ch
      [(or 'EOF (? char-whitespace?))
       (symtok)]
      [(or (? char-alphabetic?) (? char-numeric?))
       (accumulate-and-switch-state atom)]
      [(or  #\_ #\/ #\. #\- #\+)
       (accumulate-and-switch-state atom-or-sym)]
      [_
       (symtok)]))

  (define (ending-dot-count str)
    (define (edc index)
      (cond [(< index 0) 0]
            [(eqv? (string-ref str index) #\.) (add1 (edc (sub1 index)))]
            [else 0]))
    (edc (sub1 (string-length str))))

  (define (atom)
    (enter 'atom ch)
    (match ch
      [(and (? char?)
            (or (? char-alphabetic?)
                (? char-numeric?)
                #\_ #\/ #\. #\- #\+))
       (accumulate-and-switch-state atom)]
      [_
       (if (token-ends-with? #\.)
           (let* ([tokstr (collect-chars)]
                  [dotcount (ending-dot-count tokstr)])
             (backward dotcount)
             (pause mode)
             (explicit-atom-token
              (substring tokstr 0 (- (string-length tokstr) dotcount))))
           (finish-token atom-token))]))

  (define (num)
    (enter 'num ch)
    (match ch
      [(and (? char?) (? char-numeric?))
       (accumulate-and-switch-state num)]
      [#\.
       (next maybe-float)]
      [#\/
       (accumulate-and-switch-state fraction)]
      [#\i
       (handle-num-imag)]
      [_
       (pause mode)
       (num-token)]))

  (define (maybe-float)
    (enter 'maybe-float ch)
    (match ch
      [(and (? char?) (? char-numeric?))
       (accumulate #\.)
       (accumulate-and-switch-state float)]
      [#\i
       (handle-num-imag)]
      [_
       (backward 1)
       (finish-token num-token)]))

  (define (float)
    (enter 'float ch)
    (match ch
      [(and (? char?) (? char-numeric?))
       (accumulate-and-switch-state float)]
      [#\i
       (handle-num-imag)]
      [_
       (finish-token num-token)]))

  (define (fraction)
    (enter 'fraction ch)
    (match ch
           [(and (? char?) (? char-numeric?))
            (accumulate-and-switch-state fraction)]
           [#\i
            (handle-num-imag)]
           [_
            (finish-token num-token)]))

  (define (funky-atom)
    (enter 'funky-atom ch)
    (match ch
           ['EOF
            (finish-token funky-atom-token)]
           [#\'
            (accumulate ch)
            (next-char)
            (finish-token funky-atom-token)]
           [#\\
            (next-char)
            (accumulate-and-switch-state funky-atom)]
           [_
            (accumulate-and-switch-state funky-atom)]))

  (next-char)
  (cond [(eq? initial-mode 'colon)
         (pause start)
         (set! mode start)]
        [#t
         (pause str-start)
         (set! mode str-start)])
  (log-mllex-debug "STARTING: ~a" item)
  (lambda () (stacks) (resume)))

(module+ test
         (require rackunit)

         ;; Generate a lexer on a string with a wrapper that allows the request
         ;; of the car n tokens.
         ;; Example: ((tokgen "1 2 3" 'colon) 2) =>
         ;;          (<token <num 1>> <token <num 2>>)
         (define (tokgen item mode)
           (let ([lexer (mllex item mode)])
             (lambda (num-tokens)
               (let loop ([token-count num-tokens] [result '()])
                 (cond [(< token-count 1) '()]
                       [(= token-count 1) (reverse (cons (lexer) result))]
                       [else
                        (loop (sub1 token-count) (cons (lexer) result))])))))

         ;; Create all the necessary position structures to return a correct
         ;; positional token when the test string contains only one line
         (define (one-line-pos tok start end)
           (position-token tok (position start 1 start) (position end 1 end)))

         ;; Compare the car 'count' tokens lexed from 'item' with the
         ;; tokens that are the remaining arguments in 'tokens'
         (define (check-toks item count . tokens)
           (log-mllex-debug "CHECKING: ~a" item)
           (check-equal? ((tokgen item 'colon) count) tokens))

         ;; Compare the car 'count' tokens lexed from 'item' in str
         ;; mode with the tokens that are the remaining arguments in
         ;; 'tokens'
         (define (check-shell-toks item count . tokens)
           (log-mllex-debug "CHECKING: ~a" item)
           (check-equal? ((tokgen item 'default) count) tokens))

         (check-toks "28" 1 (one-line-pos (token-NUM 28) 1 3))
         (check-toks "28.6" 1 (one-line-pos (token-NUM 28.6) 1 5))
         (check-toks "28/6" 1 (one-line-pos (token-NUM 14/3) 1 5))
         (check-toks "28+6i" 3
                     (one-line-pos (token-NUM 28) 1 3)
                     (one-line-pos '+ 3 4)
                     (one-line-pos (token-NUM +6i) 4 6))
         (check-toks "28-6i" 3
                     (one-line-pos (token-NUM 28) 1 3)
                     (one-line-pos '- 3 4)
                     (one-line-pos (token-NUM +6i) 4 6))
         (check-toks "28.496+6i" 3
                     (one-line-pos (token-NUM 28.496) 1 7)
                     (one-line-pos '+ 7 8)
                     (one-line-pos (token-NUM +6i) 8 10))
         (check-toks "28.496+6.496i" 3
                     (one-line-pos (token-NUM 28.496) 1 7)
                     (one-line-pos '+ 7 8)
                     (one-line-pos (token-NUM +6.496i) 8 14))
         (check-toks "-" 1 (one-line-pos '- 1 2))
         (check-toks "-28" 2
                       (one-line-pos '- 1 2)
                       (one-line-pos (token-NUM 28) 2 4))
         (check-toks "-28.6" 2
                       (one-line-pos '- 1 2)
                       (one-line-pos (token-NUM 28.6) 2 6))
         (check-toks "-28/6" 2
                       (one-line-pos '- 1 2)
                       (one-line-pos (token-NUM 28/6) 2 6))
         (check-toks "-28+6i" 4
                     (one-line-pos '- 1 2)
                     (one-line-pos (token-NUM 28) 2 4)
                     (one-line-pos '+ 4 5)
                     (one-line-pos (token-NUM +6i) 5 7))
         (check-toks "-28-6i" 4
                     (one-line-pos '- 1 2)
                     (one-line-pos (token-NUM 28) 2 4)
                     (one-line-pos '- 4 5)
                     (one-line-pos (token-NUM +6i) 5 7))
         (check-toks "-28.496-6i" 4
                     (one-line-pos '- 1 2)
                     (one-line-pos (token-NUM 28.496) 2 8)
                     (one-line-pos '- 8 9)
                     (one-line-pos (token-NUM +6i) 9 11))
         (check-toks "-28.496+6i" 4
                     (one-line-pos '- 1 2)
                     (one-line-pos (token-NUM 28.496) 2 8)
                     (one-line-pos '+ 8 9)
                     (one-line-pos (token-NUM +6i) 9 11))
         (check-toks "-28.496+6.496i" 4
                     (one-line-pos '- 1 2)
                     (one-line-pos (token-NUM 28.496) 2 8)
                     (one-line-pos '+ 8 9)
                     (one-line-pos (token-NUM +6.496i) 9 15))
         (check-toks "-28/6i" 2
                     (one-line-pos '- 1 2)
                     (one-line-pos (token-NUM +28/6i) 2 7))
         (check-equal? ((mllex "'-+x2+5-8'" 'colon))
                       (position-token (token-ATOM "-+x2+5-8")
                                       (position 1 1 1)
                                       (position 11 1 11)))
         (check-equal? ((mllex "'-+x2\\'+5-8'" 'colon))
                       (position-token (token-ATOM "-+x2'+5-8")
                                       (position 1 1 1)
                                       (position 13 1 13)))
         (check-toks "$34" 1 (one-line-pos (token-VAR '$34) 1 4))
         (check-toks "$x34" 1 (one-line-pos (token-VAR '$x34) 1 5))
         (check-toks "${x34isthevar}" 1
                     (one-line-pos (token-VAR '$x34isthevar) 1 15))
         (check-toks "....=!3" 4
                     (one-line-pos (token-DOTDOTDOT) 1 4)
                     (one-line-pos (token-DOT) 4 5)
                     (one-line-pos '=! 5 7)
                     (one-line-pos (token-NUM 3) 7 8))
         (check-toks ".....=!3" 4
                     (one-line-pos (token-DOTDOTDOT) 1 4)
                     (one-line-pos (token-DOTDOT) 4 6)
                     (one-line-pos '=! 6 8)
                     (one-line-pos (token-NUM 3) 8 9))
         (check-toks "....=! 3" 4
                     (one-line-pos (token-DOTDOTDOT) 1 4)
                     (one-line-pos (token-DOT) 4 5)
                     (one-line-pos '=! 5 7)
                     (one-line-pos (token-NUM 3) 8 9))
         (check-toks "\"this is a \\\" str\"" 3
                     (one-line-pos (token-STRBOUND) 1 2)
                     (one-line-pos (token-STR "this is a \" str") 2 18)
                     (one-line-pos (token-STRBOUND) 18 19))
         (check-toks "%%%+3" 3
                     (one-line-pos (token-ANON '%%%) 1 4)
                     (one-line-pos '+ 4 5)
                     (one-line-pos (token-NUM 3) 5 6))
         (check-toks "%?+3" 3
                     (one-line-pos (token-COUNT) 1 3)
                     (one-line-pos '+ 3 4)
                     (one-line-pos (token-NUM 3) 4 5))
         ;; (check-toks "$\"this is a \\\" str\"" 1
         ;;             (one-line-pos (token-REGEX "this is a \" str") 1 20))
         (check-toks ":3." 3
                     (one-line-pos ': 1 2)
                     (one-line-pos (token-NUM 3) 2 3)
                     (one-line-pos (token-DOT) 3 4))
         (check-toks "?x" 1 (one-line-pos (token-CHAR #\x) 1 3))
         (check-toks "?\\t" 1 (one-line-pos (token-CHAR #\tab) 1 4))
         (check-shell-toks ";" 1 (one-line-pos (token-SEMI) 1 2))
         (check-shell-toks "|" 1 (one-line-pos (token-PIPE) 1 2))
         (check-shell-toks "<" 1 (one-line-pos (token-LT) 1 2))
         (check-shell-toks "&" 1 (one-line-pos (token-AMP) 1 2))
         (check-shell-toks "&&" 1 (one-line-pos (token-AMPAMP) 1 3))
         (check-shell-toks "; & |  <" 4
                           (one-line-pos (token-SEMI) 1 2)
                           (one-line-pos (token-AMP) 3 4)
                           (one-line-pos (token-PIPE) 5 6)
                           (one-line-pos (token-LT) 8 9))
         (check-shell-toks "\"this is a test\"&" 4
                           (one-line-pos (token-STRBOUND) 1 2)
                           (one-line-pos (token-STR "this is a test") 2 16)
                           (one-line-pos (token-STRBOUND) 16 17)
                           (one-line-pos (token-AMP) 17 18))
         (check-shell-toks "'this is a test'&" 2
                           (one-line-pos (token-FUNKYATOM "this is a test")
                                         1 17)
                           (one-line-pos (token-AMP) 17 18))
         (check-shell-toks "'this is a test' $foo${x} $3 > >> &" 11
                           (one-line-pos (token-FUNKYATOM "this is a test")
                                         1 17)
                           (one-line-pos (token-ATOMBOUND) 18 18)
                           (one-line-pos (token-VAR '$foo) 18 22)
                           (one-line-pos (token-VAR '$x) 22 26)
                           (one-line-pos (token-STRBOUND) 26 27)
                           (one-line-pos (token-ATOMBOUND) 27 27)
                           (one-line-pos (token-VAR '$3) 27 29)
                           (one-line-pos (token-STRBOUND) 29 30)
                           (one-line-pos (token-GT) 30 31)
                           (one-line-pos (token-GTGT) 32 34)
                           (one-line-pos (token-AMP) 35 36)))
;(trace mllex)