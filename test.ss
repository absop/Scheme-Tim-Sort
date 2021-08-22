(let ()
  (define (vector-ordered? lt? v)
    (let ([end (fx- (vector-length v) 1)])
      (if (fx> end 0)
          (let loop ([i 0])
            (cond
              [(fx>= i end) #t]
              [(lt? (vector-ref v i)
                    (vector-ref v (fx+ i 1)))
               (loop (fx+ i 1))]
              [else #f]))
          #t)))

  (define (make-random-vector n range)
    (let ([v (make-vector n)])
      (let loop ([i 0])
        (when (fx< i n)
              (vector-set! v i (random range))
              (loop (fx+ i 1))))
      v))

  (define (make-pair-vector m n)
    (let ([v (make-vector n)])
      (let loop ([i 0])
        (if (fx< i n)
            (let ()
              (vector-set! v i (cons (mod i m) i))
              (loop (+ i 1)))
            v))))

  (define (uninplace sort!)
    (lambda (cmp v)
      (let ([v (vector-copy v)])
        (sort! cmp v)
        v)))

  (define-syntax (bench x)
    (define (join-name prefix suffix)
      (datum->syntax #'bench
        (string->symbol (format "~a-~a" prefix suffix))))

    (define (remove-tail-bang name)
      (datum->syntax #'bench
        (let ([name (symbol->string name)])
          (string->symbol
            (string-truncate! name (- (string-length name) 1))))))

    (syntax-case x ()
      [(_ sort! size range)
       (with-syntax
         ([sort (remove-tail-bang (datum sort!))]
          [test (join-name 'bench (datum sort!))])
         #'(let ([v (make-random-vector size range)])
             (define sort (uninplace sort!))
             (define-syntax test/count-cmp
               (syntax-rules ()
                 [(_ cmp ord)
                  (let ([c 0])
                    (sort (lambda (x y) (inc! c) (cmp x y)) v)
                    (time (sort! cmp v))
                    (printf "comparations: ~a, ordered: ~a\n" c
                            (vector-ordered? ord v)))]))
             (define (test)
               (test/count-cmp <  <=)
               (test/count-cmp <  <=)
               (test/count-cmp >= >=)
               (test/count-cmp <= <=))
             (time (test))
             (newline)))]))

  (define (uncurry f)
    (lambda (values) (apply f values)))

  ;; stability
  (let ([v (make-pair-vector 3 6)])
    (printf "Check stability with v: ~a\n" v)
    (for-each
      (uncurry
        (lambda (sym cmp)
          (let ([cmp (lambda (x y) (cmp (car x) (car y)))])
            (for-each
              (uncurry
                (lambda (name sort)
                  (printf "    (~11a ~2a v): ~a\n" name sym (sort cmp v))))
              `([tim-sort    ,(uninplace tim-sort!)]
                [vector-sort ,(uninplace vector-sort!)]))
            (newline))))
      `([<  ,< ]
        [>  ,> ]
        [<= ,<=]
        [>= ,>=]))
    (newline))

  ;; Time & Comparations
  (let ([size 10000000]
        [range 1000000])
    (printf "Bench with size=~a, range=~a\n" size range)
    (bench    tim-sort! size range)
    (bench vector-sort! size range))
)
