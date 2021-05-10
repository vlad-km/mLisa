;;; -*- mode:lisp; coding:utf-8 -*-

;;; This file is part of LISA, the Lisp-based Intelligent Software
;;; Agents platform.
;;; Copyright (C) 2000 David E. Young (de.young@computer.org)

;;; Modification for JSCL under Electron platform
;;; Copyright (C) 2021 Vladimir K. Mezentsev (@vlad-km)


;;; File: node2-test.lisp

;;; GENERIC
(defgeneric increment-use-count (shared-node))
;;;(defgeneric decrement-use-count (shared-node))
(defgeneric node-use-count (shared-node))
(defgeneric node-referenced-p (shared-node))
(defgeneric pass-token-to-successors (shared-node token))
(defgeneric accept-token (terminal-node add-token))
(defgeneric add-successor (node1 node1 connector))
(defgeneric remove-successor (node1 successor-node))
(defgeneric accept-token (node1 token))
(defgeneric test-tokens (join-node left-tokens right-token))
(defgeneric pass-tokens-to-successor (join-node left-tokens))
(defgeneric combine-tokens (token token))
(defgeneric add-successor (join-node successor-node connector))
(defgeneric join-node-add-test (join-node test))
(defgeneric clear-memories (join-node))
(defgeneric accept-tokens-from-left (node token))
(defgeneric accept-token-from-left (join-node reset-token))
(defgeneric accept-token-from-right (join-node reset-token))
(defgeneric test-against-right-memory (node2 left-tokens))
(defgeneric test-against-left-memory (node2 add-token))
;;;(defgeneric remove-node-from-parent (rete-network parent child))
(defgeneric add-successor (parent new-node connector))
;;;(defgeneric decrement-use-count (join-node))
;;;(defgeneric find-existing-successor (shared-node  node1))
;;;(defgeneric add-node-set (parent node &optional count-p ))

;;; CLASSES

(defclass shared-node ()
  ((successors :initform (make-hash-table :test #'equal)
               :reader shared-node-successors)
   (refcnt :initform 0
           :accessor shared-node-refcnt)))
(defclass terminal-node ()
  ((rule :initarg :rule
         :initform nil
         :reader terminal-node-rule)))
(defclass node1 (shared-node)
  ((test :initarg :test
         :reader node1-test)))
(defclass join-node ()
  ((successor :initform nil
              :accessor join-node-successor)
   (logical-block :initform nil
                  :reader join-node-logical-block)
   (tests :initform (list)
          :accessor join-node-tests)
   (left-memory :initform (make-hash-table :test #'equal)
                :reader join-node-left-memory)
   (right-memory :initform (make-hash-table :test #'equal)
                 :reader join-node-right-memory)))
(defclass node2 (join-node) ())
(defclass node2-not (join-node) ())
(defclass node2-test (join-node) ())
(defclass node2-exists (join-node) ())
(defclass rete-network ()
  ((root-nodes :initform (make-hash-table)
               :initarg :root-nodes
               :reader rete-roots)
   (node-test-cache :initform (make-hash-table :test #'equal)
                    :initarg :node-test-cache
                    :reader node-test-cache)))


;;;;;; METHODS

(defmethod accept-tokens-from-left ((self node2-test) (left-tokens add-token))
  (add-tokens-to-left-memory self left-tokens)
  (when (every #'(lambda (test)
                   (funcall test left-tokens))
               (join-node-tests self))
    (pass-tokens-to-successor self (combine-tokens left-tokens self))))

(defmethod accept-tokens-from-left ((self node2-test) (left-tokens remove-token))
  (when (remove-tokens-from-left-memory self left-tokens)
    (pass-tokens-to-successor self (combine-tokens left-tokens self))))

(defun make-node2-test ()
  (make-instance 'node2-test))

;;; File: shared-node.lisp

#+nil
(defclass shared-node ()
  ((successors :initform (make-hash-table :test #'equal)
               :reader shared-node-successors)
   (refcnt :initform 0
           :accessor shared-node-refcnt)))

(defmethod increment-use-count ((self shared-node))
  (incf (shared-node-refcnt self)))

#+nil
(defmethod decrement-use-count ((self shared-node))
  (decf (shared-node-refcnt self)))

(defmethod node-use-count ((self shared-node))
  (shared-node-refcnt self))

(defmethod node-referenced-p ((self shared-node))
  (plusp (node-use-count self)))

#+nil
(defmethod pass-token-to-successors ((self shared-node) token)
  (loop for successor being the hash-values of (shared-node-successors self)
        do (funcall (successor-connector successor)
                    (successor-node successor)
                    token)))

(defmethod pass-token-to-successors ((self shared-node) token)
  (loop for successor in (jscl::hash-table-values (shared-node-successors self))
        do (funcall (successor-connector successor)
                    (successor-node successor)
                    token)))

#+nil
(defun shared-node-successor-nodes (shared-node)
  (loop for successor being the hash-values of (shared-node-successors shared-node)
        collect (successor-node successor)))

(defun shared-node-successor-nodes (shared-node)
  (loop for successor in (jscl::hash-table-values (shared-node-successors shared-node))
        collect (successor-node successor)))

#+nil
(defun shared-node-all-successors (shared-node)
  (loop for successor being the hash-values of (shared-node-successors shared-node)
        collect successor))

(defun shared-node-all-successors (shared-node)
  (loop for successor in (jscl::hash-table-values (shared-node-successors shared-node))
        collect successor))


;;; File: successor.lisp
(defun make-successor (node connector)
  (cons node connector))

(defun successor-node (successor)
  (car successor))

(defun successor-connector (successor)
  (cdr successor))

(defun call-successor (successor &rest args)
  (apply #'funcall 
         (successor-connector successor)
         (successor-node successor)
         args))

;;; File: node-pair.lisp
(defun make-node-pair (child parent)
  (cons child parent))

(defun node-pair-child (node-pair)
  (car node-pair))

(defun node-pair-parent (node-pair)
  (cdr node-pair))


;;; File: terminal-node.lisp

#+nil
(defclass terminal-node ()
  ((rule :initarg :rule
         :initform nil
         :reader terminal-node-rule)))

(defmethod accept-token ((self terminal-node) (tokens add-token))
  (let* ((rule (terminal-node-rule self))
         (activation (make-activation rule tokens)))
    (add-activation (rule-engine rule) activation)
    (bind-rule-activation rule activation tokens)
    t))

(defmethod accept-token ((self terminal-node) (tokens remove-token))
  (let* ((rule (terminal-node-rule self))
         (activation (find-activation-binding rule tokens)))
    (unless (null activation)
      (disable-activation (rule-engine rule) activation)
      (unbind-rule-activation rule tokens))
    t))

(defmethod accept-token ((self terminal-node) (token reset-token))
  (clear-activation-bindings (terminal-node-rule self))
  t)

#+nil
(defmethod print-object ((self terminal-node) strm)
  (print-unreadable-object (self strm :type t)
    (format strm "~A" (rule-name (terminal-node-rule self)))))

(defun make-terminal-node (rule)
  (make-instance 'terminal-node :rule rule))

;;; File: node1.lisp

#+nil
(defclass node1 (shared-node)
  ((test :initarg :test
         :reader node1-test)))

(defmethod add-successor ((self node1) (new-node node1) connector)
  (with-slots ((successor-table successors)) self
    (let ((successor (gethash (node1-test new-node) successor-table)))
      (when (null successor)
        (setf successor
          (setf (gethash (node1-test new-node) successor-table)
            (make-successor new-node connector))))
      (successor-node successor))))

(defmethod add-successor ((self node1) (new-node t) connector)
  (setf (gethash `(,new-node ,connector) (shared-node-successors self))
    (make-successor new-node connector))
  new-node)

(defmethod remove-successor ((self node1) successor-node)
  (let ((successors (shared-node-successors self)))
    (maphash #'(lambda (key successor)
                 (when (eq successor-node (successor-node successor))
                   (remhash key successors)))
             successors)
    successor-node))

(defmethod accept-token ((self node1) token)
  (if (funcall (node1-test self) token)
      (pass-token-to-successors self token)
    nil))

(defmethod accept-token ((self node1) (token reset-token))
  (pass-token-to-successors self (token-push-fact token t)))

#+nil
(defmethod print-object ((self node1) strm)
  (print-unreadable-object (self strm :type t :identity t)
    (format strm "~S ; ~D" (node1-test self) (node-use-count self))))

(defun make-node1 (test)
  (make-instance 'node1 :test test))


;;; File: join-node.lisp
#+nil
(defclass join-node ()
  ((successor :initform nil
              :accessor join-node-successor)
   (logical-block :initform nil
                  :reader join-node-logical-block)
   (tests :initform (list)
          :accessor join-node-tests)
   (left-memory :initform (make-hash-table :test #'equal)
                :reader join-node-left-memory)
   (right-memory :initform (make-hash-table :test #'equal)
                 :reader join-node-right-memory)))

(defun mark-as-logical-block (join-node marker)
  (setf (slot-value join-node 'logical-block) marker))

(defun logical-block-p (join-node)
  (numberp (join-node-logical-block join-node)))

(defun remember-token (memory token)
  (setf (gethash (hash-key token) memory) token))

(defun forget-token (memory token)
  (remhash (hash-key token) memory))

(defun add-tokens-to-left-memory (join-node tokens)
  (remember-token (join-node-left-memory join-node) tokens))

(defun add-token-to-right-memory (join-node token)
  (remember-token (join-node-right-memory join-node) token))

(defun remove-tokens-from-left-memory (join-node tokens)
  (forget-token (join-node-left-memory join-node) tokens))

(defun remove-token-from-right-memory (join-node token)
  (forget-token (join-node-right-memory join-node) token))

(defun left-memory-count (join-node)
  (hash-table-count (join-node-left-memory join-node)))

(defun right-memory-count (join-node)
  (hash-table-count (join-node-right-memory join-node)))

(defmethod test-tokens ((self join-node) left-tokens right-token)
  (token-push-fact left-tokens (token-top-fact right-token))
  (prog1
      (every #'(lambda (test)
                 (funcall test left-tokens))
             (join-node-tests self))
    (token-pop-fact left-tokens)))

(defmethod pass-tokens-to-successor ((self join-node) left-tokens)
  (call-successor (join-node-successor self) left-tokens))

(defmethod combine-tokens ((left-tokens token) (right-token token))
  (token-push-fact (replicate-token left-tokens) (token-top-fact right-token)))

(defmethod combine-tokens ((left-tokens token) (right-token t))
  (token-push-fact (replicate-token left-tokens) right-token))

(defmethod add-successor ((self join-node) successor-node connector)
  (setf (join-node-successor self)
    (make-successor successor-node connector)))

(defmethod join-node-add-test ((self join-node) test)
  (push test (join-node-tests self)))

(defmethod clear-memories ((self join-node))
  (clrhash (join-node-left-memory self))
  (clrhash (join-node-right-memory self)))

(defmethod accept-tokens-from-left ((self join-node) (left-tokens reset-token))
  (clear-memories self)
  (pass-tokens-to-successor self left-tokens))

(defmethod accept-token-from-right ((self join-node) (left-tokens reset-token))
  nil)

#+nil
(defmethod print-object ((self join-node) strm)
  (print-unreadable-object (self strm :type t :identity t)
    (format strm "left ~S ; right ~S ; tests ~S"
            (left-memory-count self)
            (right-memory-count self)
            (length (join-node-tests self)))))

;;; File: node2.lisp

#+nil
(defclass node2 (join-node) ())

#+nil
(defmethod test-against-right-memory ((self node2) left-tokens)
  (loop for right-token being the hash-values of (join-node-right-memory self)
      do (when (test-tokens self left-tokens right-token)
           (pass-tokens-to-successor 
            self (combine-tokens left-tokens right-token)))))

(defmethod test-against-right-memory ((self node2) left-tokens)
  (loop for right-token in (jscl::hash-table-values (join-node-right-memory self))
      do (when (test-tokens self left-tokens right-token)
           (pass-tokens-to-successor 
            self (combine-tokens left-tokens right-token)))))

#+nil
(defmethod test-against-left-memory ((self node2) (right-token add-token))
  (loop for left-tokens being the hash-values of (join-node-left-memory self)
      do (when (test-tokens self left-tokens right-token)
           (pass-tokens-to-successor 
            self (combine-tokens left-tokens right-token)))))

(defmethod test-against-left-memory ((self node2) (right-token add-token))
  (loop for left-tokens in (jscl::hash-table-values (join-node-left-memory self))
        do (when (test-tokens self left-tokens right-token)
             (pass-tokens-to-successor 
              self (combine-tokens left-tokens right-token)))))

#+nil
(defmethod test-against-left-memory ((self node2) (right-token remove-token))
  (loop for left-tokens being the hash-values of (join-node-left-memory self)
      do (when (test-tokens self left-tokens right-token)
           (pass-tokens-to-successor
            self (combine-tokens
                  (make-remove-token left-tokens) right-token)))))

(defmethod test-against-left-memory ((self node2) (right-token remove-token))
  (loop for left-tokens in (jscl::hash-table-values (join-node-left-memory self))
        do (when (test-tokens self left-tokens right-token)
             (pass-tokens-to-successor
              self (combine-tokens
                    (make-remove-token left-tokens) right-token)))))

(defmethod accept-tokens-from-left ((self node2) (left-tokens add-token))
  (add-tokens-to-left-memory self left-tokens)
  (test-against-right-memory self left-tokens))

(defmethod accept-token-from-right ((self node2) (right-token add-token))
  (add-token-to-right-memory self right-token)
  (test-against-left-memory self right-token))

(defmethod accept-tokens-from-left ((self node2) (left-tokens remove-token))
  (when (remove-tokens-from-left-memory self left-tokens)
    (test-against-right-memory self left-tokens)))

(defmethod accept-token-from-right ((self node2) (right-token remove-token))
  (when (remove-token-from-right-memory self right-token)
    (test-against-left-memory self right-token)))

(defun make-node2 ()
  (make-instance 'node2))

;;; File: node2-not.lisp

#+nil
(defclass node2-not (join-node) ())

#+nil
(defmethod test-against-right-memory ((self node2-not) left-tokens)
  (loop for right-token being the hash-values of (join-node-right-memory self)
        do (when (test-tokens self left-tokens right-token)
             (token-increment-not-counter left-tokens)))
  (unless (token-negated-p left-tokens)
    (pass-tokens-to-successor 
     self (combine-tokens left-tokens self))))

(defmethod test-against-right-memory ((self node2-not) left-tokens)
  (loop for right-token in (jscl::hash-table-values (join-node-right-memory self))
        do (when (test-tokens self left-tokens right-token)
             (token-increment-not-counter left-tokens)))
  (unless (token-negated-p left-tokens)
    (pass-tokens-to-successor 
     self (combine-tokens left-tokens self))))

#+nil
(defmethod test-against-left-memory ((self node2-not) (right-token add-token))
  (loop for left-tokens being the hash-values of (join-node-left-memory self)
        do (when (test-tokens self left-tokens right-token)
             (token-increment-not-counter left-tokens)
             (pass-tokens-to-successor 
              self (combine-tokens (make-remove-token left-tokens) self)))))

(defmethod test-against-left-memory ((self node2-not) (right-token add-token))
  (loop for left-tokens in (jscl::hash-table-values (join-node-left-memory self))
        do (when (test-tokens self left-tokens right-token)
             (token-increment-not-counter left-tokens)
             (pass-tokens-to-successor 
              self (combine-tokens (make-remove-token left-tokens) self)))))
  
#+nil
(defmethod test-against-left-memory ((self node2-not)(right-token remove-token))
  (loop for left-tokens being the hash-values of (join-node-left-memory self)
        do (when (and (test-tokens self left-tokens right-token)
                      (not (token-negated-p
                            (token-decrement-not-counter left-tokens))))
             (pass-tokens-to-successor 
              self (combine-tokens left-tokens self)))))

(defmethod test-against-left-memory ((self node2-not)(right-token remove-token))
  (loop for left-tokens in (jscl::hash-table-values (join-node-left-memory self))
        do (when (and (test-tokens self left-tokens right-token)
                      (not (token-negated-p
                            (token-decrement-not-counter left-tokens))))
             (pass-tokens-to-successor 
              self (combine-tokens left-tokens self)))))
  
(defmethod accept-tokens-from-left ((self node2-not) (left-tokens add-token))
  (add-tokens-to-left-memory self left-tokens)
  (test-against-right-memory self left-tokens))

(defmethod accept-tokens-from-left ((self node2-not) (left-tokens remove-token))
  (when (remove-tokens-from-left-memory self left-tokens)
    (pass-tokens-to-successor self (combine-tokens left-tokens self))))

(defmethod accept-token-from-right ((self node2-not) (right-token add-token))
  (add-token-to-right-memory self right-token)
  (test-against-left-memory self right-token))

(defmethod accept-token-from-right ((self node2-not) (right-token remove-token))
  (when (remove-token-from-right-memory self right-token)
    (test-against-left-memory self right-token)))

(defun make-node2-not ()
  (make-instance 'node2-not))

;;; File: node2-test.lisp
#+nil (defclass node2-test (join-node) ())

(defmethod accept-tokens-from-left ((self node2-test) (left-tokens add-token))
  (add-tokens-to-left-memory self left-tokens)
  (when (every #'(lambda (test)
                   (funcall test left-tokens))
               (join-node-tests self))
    (pass-tokens-to-successor self (combine-tokens left-tokens self))))

(defmethod accept-tokens-from-left ((self node2-test) (left-tokens remove-token))
  (when (remove-tokens-from-left-memory self left-tokens)
    (pass-tokens-to-successor self (combine-tokens left-tokens self))))

(defun make-node2-test ()
  (make-instance 'node2-test))

;;; File: node2-exists.lisp
#+nil (defclass node2-exists (join-node) ())


#+nil
(defmethod test-against-right-memory ((self node2-exists) (left-tokens add-token))
  (loop for right-token being the hash-values of (join-node-right-memory self)
        do (when (test-tokens self left-tokens right-token)
             (token-increment-exists-counter left-tokens)
             (pass-tokens-to-successor 
              self (combine-tokens left-tokens right-token)))))

(defmethod test-against-right-memory ((self node2-exists) (left-tokens add-token))
  (maphash
   (lambda (ignore right-token)
     (when (test-tokens self left-tokens right-token)
       (token-increment-exists-counter left-tokens)
       (pass-tokens-to-successor 
        self (combine-tokens left-tokens right-token))))
   (join-node-right-memory self)))


#+nil
(defmethod test-against-right-memory ((self node2-exists) (left-tokens remove-token))
  (loop for right-token being the hash-values of (join-node-right-memory self)
        do (when (test-tokens self left-tokens right-token)
             (pass-tokens-to-successor 
              self (combine-tokens left-tokens right-token)))))

(defmethod test-against-right-memory ((self node2-exists) (left-tokens add-token))
  (maphash
   (lambda (ignore right-token)
     (when (test-tokens self left-tokens right-token)
       (pass-tokens-to-successor 
        self (combine-tokens left-tokens right-token))))
   (join-node-right-memory self)))

#+nil
(defmethod test-against-left-memory ((self node2-exists) (right-token add-token))
  (loop for left-tokens being the hash-values of (join-node-left-memory self)
        do (when (and (test-tokens self left-tokens right-token)
                      (= (token-increment-exists-counter left-tokens) 1))
             (pass-tokens-to-successor 
              self (combine-tokens left-tokens right-token)))))

(defmethod test-against-left-memory ((self node2-exists) (right-token add-token))
  (maphash
   (lambda (ignore left-token)
     (when (and (test-tokens self left-tokens right-token)
                (= (token-increment-exists-counter left-tokens) 1))
       (pass-tokens-to-successor 
        self (combine-tokens left-tokens right-token))))
   (join-node-left-memory self)))

#+nil
(defmethod test-against-left-memory ((self node2-exists) (right-token remove-token))
  (loop for left-tokens being the hash-values of (join-node-left-memory self)
        do (when (test-tokens self left-tokens right-token)
             (token-decrement-exists-counter left-tokens)
             (pass-tokens-to-successor
              self (combine-tokens
                    (make-remove-token left-tokens) right-token)))))

(defmethod test-against-left-memory ((self node2-exists) (right-token remove-token))
  (maphash
   (lambda (ignore left-token)
     (when (test-tokens self left-tokens right-token)
       (token-decrement-exists-counter left-tokens)
       (pass-tokens-to-successor
        self (combine-tokens
              (make-remove-token left-tokens) right-token))))
   (join-node-left-memory self)))

(defmethod accept-tokens-from-left ((self node2-exists) (left-tokens add-token))
  (add-tokens-to-left-memory self left-tokens)
  (test-against-right-memory self left-tokens))

(defmethod accept-token-from-right ((self node2-exists) (right-token add-token))
  (add-token-to-right-memory self right-token)
  (test-against-left-memory self right-token))

(defmethod accept-tokens-from-left ((self node2-exists) (left-tokens remove-token))
  (when (remove-tokens-from-left-memory self left-tokens)
    (test-against-right-memory self left-tokens)))

(defmethod accept-token-from-right ((self node2-exists) (right-token remove-token))
  (when (remove-token-from-right-memory self right-token)
    (test-against-left-memory self right-token)))

(defun make-node2-exists ()
  (make-instance 'node2-exists))


;;; File: rete-compiler.lisp
(defvar *root-nodes* nil)
(defvar *rule-specific-nodes* nil)
(defvar *leaf-nodes* nil)
(defvar *logical-block-marker*)

(defun set-leaf-node (node address) (setf (aref *leaf-nodes* address) node))
(defun leaf-node () (aref *leaf-nodes* (1- (length *leaf-nodes*))))
(defun left-input (address) (aref *leaf-nodes* (1- address)))
(defun right-input (address)  (aref *leaf-nodes* address))
(defun logical-block-marker () *logical-block-marker*)
  
#+nil
(defclass rete-network ()
  ((root-nodes :initform (make-hash-table)
               :initarg :root-nodes
               :reader rete-roots)
   (node-test-cache :initform (make-hash-table :test #'equal)
                    :initarg :node-test-cache
                    :reader node-test-cache)))

(defun record-node (node parent)
  (when (typep parent 'shared-node) (increment-use-count parent))
  (push (make-node-pair node parent) *rule-specific-nodes*)
  node)

#+nil
(defmethod remove-node-from-parent ((self rete-network)(parent t) child)
  (remhash (node1-test child) (rete-roots self)))
#+nil
(defmethod remove-node-from-parent ((self rete-network)(parent shared-node) child)
  (remove-successor parent child))

(defun remove-node-from-parent (self parent child)
  (typecase self
    (rete-network
     (cond ((eql parent t)
            (remhash (node1-test child) (rete-roots self)))
           ((typep parent 'shared-node)
            (remove-successor parent child))
           (t (error "remove-node-from-parent: WTF node ~a?" parent))))
    (t (error "remove-node-from-parent: WTF rete-network ~a" self))))

(defun make-root-node (class)
  (let* ((test (make-class-test class))
         (root (gethash test *root-nodes*)))
    (when (null root)
      (setf root (make-node1 test))
      (setf (gethash test *root-nodes*) root))
    (record-node root t)))

(defmethod add-successor ((parent t) new-node connector)
  ;;(declare (ignore connector))
  new-node)

(defmethod add-successor :around ((parent shared-node) new-node connector)
  ;;(declare (ignore new-node connector))
  (record-node (call-next-method) parent))

(defun make-intra-pattern-node (slot)
  (let ((test
         (cond ((simple-slot-p slot)
                (make-simple-slot-test slot))
               ((constrained-slot-p slot)
                (make-intra-pattern-constraint-test slot))
               (t
                (make-intra-pattern-test slot)))))
    (make-node1 test)))

#+nil
(defun distribute-token (rete-network token)
  (loop for root-node being the hash-values 
      of (rete-roots rete-network)
      do (accept-token root-node token)))

(defun distribute-token (rete-network token)
  (maphash
   (lambda (ignore root-node)
     (accept-token root-node token))
   (rete-roots rete-network)))


;;; note: woooooow
;;;(error "make-rete-network")
(defmethod make-rete-network (&rest args &key &allow-other-keys)
  (apply #'make-instance 'rete-network args))

;;; The following functions serve as "connectors" between any two
;;; nodes. PASS-TOKEN connects two pattern (one-input) nodes, or a join node 
;;; to a terminal node; ENTER-JOIN-NETWORK-FROM-LEFT connects a pattern node
;;; to a join node; ENTER-JOIN-NETWORK-FROM-RIGHT also connects a pattern node
;;; to a join node; both PASS-TOKENS-ON-LEFT and PASS-TOKEN-ON-RIGHT connect
;;; two join nodes.

(defun pass-token (node token)
  (accept-token node token))

(defun pass-tokens-on-left (node2 tokens)
  (accept-tokens-from-left node2 tokens))

(defun pass-token-on-right (node2 token)
  (accept-token-from-right node2 token))

(defun enter-join-network-from-left (node2 tokens)
  (pass-tokens-on-left node2 (replicate-token tokens)))

(defun enter-join-network-from-right (node2 token)
  (pass-token-on-right node2 (replicate-token token)))

;;; end connector functions

;;;  "The alpha memory nodes and tests"
(defun add-intra-pattern-nodes (patterns)
  (dolist (pattern patterns)
    (cond ((test-pattern-p pattern)
           (set-leaf-node t (parsed-pattern-address pattern)))
          (t
           (let ((node
                  (make-root-node (parsed-pattern-class pattern)))
                 (address (parsed-pattern-address pattern)))
             (set-leaf-node node address)
             (dolist (slot (parsed-pattern-slots pattern))
               (when (intra-pattern-slot-p slot)
                 (setf node
                   (add-successor node (make-intra-pattern-node slot)
                                  #'pass-token))
                 (set-leaf-node node address))))))))

(defun add-join-node-tests (join-node pattern)
  (labels ((add-simple-join-node-test (slot)
             (unless (= (binding-address (pattern-slot-slot-binding slot))
                        (parsed-pattern-address pattern))
               (join-node-add-test join-node
                                   (make-inter-pattern-test slot))))
           (add-slot-constraint-test (slot)
             (join-node-add-test join-node
                                 (make-predicate-test
                                  (pattern-slot-constraint slot)
                                  (pattern-slot-constraint-bindings slot)
                                  (negated-slot-p slot))))
           (add-test-pattern-predicate ()
             (join-node-add-test join-node
                                 (make-predicate-test
                                  (parsed-pattern-test-forms pattern)
                                  (parsed-pattern-test-bindings pattern))))
           (add-generic-pattern-tests ()
             (dolist (slot (parsed-pattern-slots pattern))
               (cond ((simple-bound-slot-p slot)
                      (add-simple-join-node-test slot))
                     ((constrained-slot-p slot)
                      (add-slot-constraint-test slot))))))
    (if (test-pattern-p pattern)
        (add-test-pattern-predicate)
      (add-generic-pattern-tests))
    join-node))

(defun make-join-node (pattern)
  (let ((join-node
         (cond ((negated-pattern-p pattern)
                (make-node2-not))
               ((test-pattern-p pattern)
                (make-node2-test))
               ((existential-pattern-p pattern)
                (make-node2-exists))
               (t (make-node2)))))
    (when (eql (parsed-pattern-address pattern) (logical-block-marker))
      (mark-as-logical-block join-node (logical-block-marker)))
    join-node))

(defun make-left-join-connection (join-node node)
  (if (typep node 'shared-node)
      (add-successor node join-node #'enter-join-network-from-left)
    (add-successor node join-node #'pass-tokens-on-left))
  join-node)

(defun make-right-join-connection (join-node node)
  (if (typep node 'shared-node)
      (add-successor node join-node #'enter-join-network-from-right)
    (add-successor node join-node #'pass-token-on-right))
  join-node)

;;;  "The beta memory nodes and tests"
(defun add-inter-pattern-nodes (patterns)
  (dolist (pattern (rest patterns))
    (let ((join-node (make-join-node pattern))
          (address (parsed-pattern-address pattern)))
      (add-join-node-tests join-node pattern)
      (make-left-join-connection join-node (left-input address))
      (make-right-join-connection join-node (right-input address))
      (set-leaf-node join-node address))))

(defun add-terminal-node (rule)
  (add-successor (leaf-node) (make-terminal-node rule) #'pass-token))

;;; addresses a problem reported by Andrew Philpot on 9/6/2007
(defun copy-node-test-table (src)
  (let ((target (make-hash-table :test #'equal)))
    (maphash (lambda (key value)
               (setf (gethash key target) value))
             src)
    target))

(defun compile-rule-into-network (rete-network patterns rule)
  (let ((*root-nodes* (rete-roots rete-network))
        (*rule-specific-nodes* (list))
        (*leaf-nodes* (make-array (length patterns)))
        (*logical-block-marker* (rule-logical-marker rule))
        (*node-test-table* (node-test-cache rete-network)))
    (add-intra-pattern-nodes patterns)
    (add-inter-pattern-nodes patterns)
    (add-terminal-node rule)
    (attach-rule-nodes rule (nreverse *rule-specific-nodes*))
    (setf (slot-value rete-network 'root-nodes) *root-nodes*)
    rete-network))

(defun merge-rule-into-network (to-network patterns rule &key (loader nil))
  (let ((from-network
         (compile-rule-into-network
          (make-rete-network :node-test-cache (copy-node-test-table (node-test-cache to-network)))
          patterns rule)))
    (when loader
      (funcall loader from-network))
    (attach-rule-nodes rule (merge-networks from-network to-network))
    to-network))

;;; File: tms.lisp
(defmethod pass-tokens-to-successor :before ((self join-node)
                                             (left-tokens remove-token))
  (when (logical-block-p self)
    (schedule-dependency-removal 
     (make-dependency-set left-tokens (join-node-logical-block self)))))

;;; File: network-ops.lisp
;;;(error "loop hash-values")
#+nil
(defun add-token-to-network (rete-network token-ctor)
  (loop for root-node being the hash-values of (rete-roots rete-network)
      do (accept-token root-node (funcall token-ctor))))

(defun add-token-to-network (rete-network token-ctor)
  (maphash (lambda (ignore root-node)
             (accept-token root-node (funcall token-ctor)))
           (rete-roots rete-network)))

(defun add-fact-to-network (rete-network fact)
  (add-token-to-network
   rete-network #'(lambda () (make-add-token fact))))

(defun remove-fact-from-network (rete-network fact)
  (add-token-to-network
   rete-network #'(lambda () (make-remove-token fact))))

(defun reset-network (rete-network)
  (add-token-to-network
   rete-network #'(lambda () (make-reset-token t))))

;;; note: wooow
#+nil (defmethod decrement-use-count ((node join-node)) 0)
#+nil (defmethod decrement-use-count ((node terminal-node)) 0)

(defun decrement-use-count (node)
  (typecase node
    (join-node 0)
    (terminal-node 0)
    (shared-node (decf (shared-node-refcnt node)))
    (t (error "WTF ~a node?" node))))

(defun remove-rule-from-network (rete-network rule)
  (labels ((remove-nodes (nodes)
             (if (endp nodes) rule
               (let ((node (node-pair-child (first nodes)))
                     (parent (node-pair-parent (first nodes))))
                 (when (zerop (decrement-use-count node))
                   (remove-node-from-parent rete-network parent node))
                 (remove-nodes (rest nodes))))))
    (remove-nodes (rule-node-list rule))))

#+nil
(defmethod find-existing-successor ((parent shared-node) (node node1))
  (gethash (node1-test node) (shared-node-successors parent)))

#+nil
(defmethod find-existing-successor (parent node)
  (declare (ignore parent node))
  nil)

(defun find-existing-successor (parent node)
  (typecase parent
    (shared-node
     (typecase node
       (node1 (gethash (node1-test node) (shared-node-successors parent)))
       (t nil))
     (t nil))))

(defvar *node-set* nil)

#+nil
(defmethod add-node-set ((parent shared-node) node &optional (count-p nil))
  (when count-p
    (increment-use-count parent))
  (push (make-node-pair node parent) *node-set*))

#+nil
(defmethod add-node-set ((parent join-node) node &optional count-p)
  (declare (ignore node count-p))
  nil)

#+nil
(defmethod add-node-set (parent node &optional count-p)
  (declare (ignore count-p))
  (push (make-node-pair node parent) *node-set*))

(defun add-node-set (parent node &optional (count-p nil))
  (typecase parent
    (shared-node
     (when count-p (increment-use-count parent))
     (push (make-node-pair node parent) *node-set*))
    (join-node nil)
    (t (push (make-node-pair node parent) *node-set*))))

(defun merge-networks (from-rete to-rete)
  (labels ((find-root-node (network node)
             (gethash (node1-test node) (rete-roots network)))
           (collect-node-sets (parent children)
             (if (endp children) parent
                 (let ((child (first children)))
                   (add-node-set parent child)
                   (when (typep child 'shared-node)
                     (collect-node-sets child 
                                        (shared-node-successor-nodes child)))
                   (collect-node-sets parent (rest children)))))
           (add-new-root (network root)
             (setf (gethash (node1-test root) (rete-roots network)) root)
             (add-node-set t root)
             (collect-node-sets root (shared-node-successor-nodes root)))
           (merge-successors (parent successors)
             (if (endp successors) parent
                 (let* ((new-successor (first successors))
                        (existing-successor 
                          (find-existing-successor parent (successor-node new-successor))))
                   (cond ((null existing-successor)
                          (add-successor parent
                                         (successor-node new-successor)
                                         (successor-connector new-successor))
                          (add-node-set parent (successor-node new-successor)))
                         (t (add-node-set parent (successor-node existing-successor) t)
                            (merge-successors 
                             (successor-node existing-successor)
                             (shared-node-all-successors 
                              (successor-node new-successor)))))
                   (merge-successors parent (rest successors)))))
           (merge-root-node (new-root)
             (let ((existing-root
                     (find-root-node to-rete new-root)))
               (cond ((null existing-root)
                      (add-new-root to-rete new-root))
                     (t
                      (add-node-set t existing-root)
                      (merge-successors
                       existing-root 
                       (shared-node-all-successors new-root)))))))
    (let ((*node-set* (list)))
;;; bug: todo: loop hash-value
      (maphash (lambda (ignore new-root) (merge-root-node new-root)) (rete-roots from-rete))
      (nreverse *node-set*))))


;;; File: network-crawler.lisp
#+nil
(defun show-network (rete-network &optional (strm *terminal-io*))
  (labels ((get-roots ()
             (loop for node being the hash-values of (rete-roots rete-network)
                   collect node))
           (get-successors (shared-node)
             (loop for s being the hash-values of (shared-node-successors shared-node) 
                   collect (successor-node s)))
           (get-successor (join-node)
             (list (successor-node (join-node-successor join-node))))
           (trace-nodes (nodes &optional (level 0))
             (unless (null nodes)
               (let* ((node (first nodes))
                      (string (format nil "~S" node)))
                 ;; bug: unreleased format syntax
                 (format strm "~V<~A~>~%" (+ level (length string)) string)
                 (typecase node
                   (shared-node
                    (trace-nodes (get-successors node) (+ level 3)))
                   (join-node
                    (trace-nodes (get-successor node) (+ level 3)))
                   (terminal-node
                    nil))
                 (trace-nodes (rest nodes) level)))))
    (trace-nodes (get-roots))))

;;; EOF
