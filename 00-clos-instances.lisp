;;; -*- mode:lisp; coding:utf-8 -*-

;;; Modification for JSCL under Electron platform
;;; Copyright (C) 2021 Vladimir K. Mezentsev (@vlad-km)

;;; from 05-core.lisp
(defclass inference-engine-object () ())

;;; "This class represents 'autoloaded' facts that are asserted automatically
;;;  as part of an inference engine reset."
(defclass deffacts ()
  ((name :initarg :name
         :reader deffacts-name)
   (fact-list :initarg :fact-list
              :initform nil
              :reader deffacts-fact-list)))

;;; "Represents a rule activation."
(defclass activation ()
  ((rule :initarg :rule
         :initform nil
         :reader activation-rule)
   (tokens :initarg :tokens
           :initform nil
           :reader activation-tokens)
   (timestamp :initform (incf *activation-timestamp*)
              :reader activation-timestamp)
   (eligible :initform t
             :accessor activation-eligible)))

;;; "Serves as the base class for all classes implementing conflict
;;;  resolution strategies."
(defclass strategy ()
  ())

(defclass priority-queue-mixin ()
  ((heap :initarg :heap
         :reader heap)))

(defclass indexed-priority-list ()
  ((priority-vector :reader get-priority-vector)
   (inodes :initform '()
           :accessor get-inodes)
   (delta :accessor get-delta)
   (insertion-function :initarg :insertion-function
                       :reader get-insertion-function)))

;;; "A base class for all LISA builtin conflict resolution strategies."
(defclass builtin-strategy (strategy priority-queue-mixin)
  ())

;;; "A depth-first conflict resolution strategy."
(defclass depth-first-strategy (builtin-strategy)
  ())

;;; "A breadth-first conflict resolution strategy."
(defclass breadth-first-strategy (builtin-strategy)
  ())

(defclass context ()
  ((name :initarg :name
         :reader context-name)
   (rules :initform (make-hash-table :test #'equal)
          :reader context-rules)
   (strategy :initarg :strategy
             :reader context-strategy)))

;;;  "Represents production rules after they've been analysed by the language
;;;  parser."
(defclass rule ()
  ((short-name :initarg :short-name
               :initform nil
               :reader rule-short-name)
   (qualified-name :reader rule-name)
   (comment :initform nil
            :initarg :comment
            :reader rule-comment)
   (salience :initform 0
             :initarg :salience
             :reader rule-salience)
   (context :initarg :context
            :reader rule-context)
   (auto-focus :initform nil
               :initarg :auto-focus
               :reader rule-auto-focus)
   (behavior :initform nil
             :initarg :behavior
             :accessor rule-behavior)
   (binding-set :initarg :binding-set
                :initform nil
                :reader rule-binding-set)
   (node-list :initform nil
              :reader rule-node-list)
   (activations :initform (make-hash-table :test #'equal)
                :accessor rule-activations)
   (patterns :initform (list)
             :initarg :patterns
             :reader rule-patterns)
   (actions :initform nil
            :initarg :actions
            :reader rule-actions)
   (logical-marker :initform nil
                   :initarg :logical-marker
                   :reader rule-logical-marker)
   (belief-factor :initarg :belief
                  :initform nil
                  :reader belief-factor)
   (active-dependencies :initform (make-hash-table :test #'equal)
                        :reader rule-active-dependencies)
   (engine :initarg :engine
           :initform nil
           :reader rule-engine)))

;;;   "Represents the canonical form of a pattern analysed by the DEFRULE parser."
(defstruct parsed-pattern
  (class nil :type symbol)
  (slots nil)
  (address 0 :type integer)
  (pattern-binding nil)
  (test-bindings nil :type list)
  (binding-set nil :type list)
  (logical nil :type symbol)
  (sub-patterns nil :type list)
  (type :generic :type symbol))

(defstruct rule-actions
  (bindings nil :type list)
  (actions nil :type list))

(defclass token ()
  ((facts :initform
          (make-array 0 :adjustable t :fill-pointer 0)
          :accessor token-facts)
   (not-counter :initform 0
                :accessor token-not-counter)
   (exists-counter :initform 0
                   :accessor token-exists-counter)
   (hash-code :initform (list)
              :accessor token-hash-code)
   (contents :initform nil
             :reader token-contents)))

(defclass add-token (token) ())
(defclass remove-token (token) ())
(defclass reset-token (token) ())

;;; 06-network.lisp
(defclass network-uid nil ((id :initform (make-network-hash-key) :reader net-hash-key)))

(defclass shared-node (network-uid)
  ((successors :initform (make-hash-table :test #'equal)
               :reader shared-node-successors)
   (refcnt :initform 0
           :accessor shared-node-refcnt)))

(defclass terminal-node (network-uid)
  ((rule :initarg :rule
         :initform nil
         :reader terminal-node-rule)))

(defclass node1 (shared-node)
  ((test :initarg :test
         :reader node1-test)))

(defclass join-node (network-uid)
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


;;;EOF
