(clear)

(deftemplate control-fact ())

(deftemplate multiple-facts ()
    (slot instancename))

(defrule broken-rule ()
    ;; NOTE: swapping the order of these two patterns fixes the problem
    (control-fact)
    (multiple-facts (instancename ?name))
    =>
    (format t "This rule shouldnt fire (instance name=~a)~%" ?name))

(defrule startup ()
    =>
    (assert> (multiple-facts (instancename first)))

    (assert> (multiple-facts (instancename second)))
    (assert> (multiple-facts (instancename third)))
    (assert> (multiple-facts (instancename fourth)))
;;;(retract (assert (control-fact))))
    (assert> (control-fact)))

;;;(watch :all)
(reset)

;;;eof